#!/usr/bin/env python3
"""Round-3 arm64 AES-CTR candidate (Go assembler syntax): two functions,

  func ctrBlocksAsm(nr int, xk *[60]uint32, dst, src *byte, n, r int, ivlo, ivhi uint64)
  func ctrBlocksEOR3Asm(nr int, xk *[60]uint32, dst, src *byte, n, r int, ivlo, ivhi uint64)

identical except for the final XOR (two EORs, or one EOR3 with FEAT_SHA3).
Each XORs n groups of G blocks and then r < G blocks (8/4/2/1 steps) of
keystream into dst. The low 64 bits of the counter must not wrap inside the
call. dst and src are equal or do not overlap.

Usage: gen_ctr_asm3.py [--blocks G] [--stage S] <original ctr_arm64.s> > ctr_arm64.s
"""
import argparse
import sys

p = argparse.ArgumentParser()
p.add_argument("orig")
p.add_argument("--blocks", type=int, default=12)
p.add_argument("--stage", type=int, default=2)
args = p.parse_args()

G = args.blocks
NKEYS = 15
KEND = G + NKEYS - 1          # last round-key register
STAGE0 = KEND + 1             # plaintext staging registers
CTR = STAGE0 + args.stage     # counter, lanes [hi, lo]
ONE = CTR + 1                 # [0, 1]
TWO = ONE + 1                 # [0, 2]
assert TWO <= 31, "register budget"

out = []
emit = out.append
v = lambda i: f"V{i}.B16"
keyreg = lambda nr, k: KEND - nr + k


def load_keys(nr):
    regs = list(range(keyreg(nr, 0), KEND + 1))
    while regs:
        chunk, regs = regs[:4], regs[4:]
        emit(f"\tVLD1.P {16*len(chunk)}(XK), [{', '.join(v(r) for r in chunk)}]")


def counters(B):
    """Counter blocks for V0..V(B-1); CTR advances by B. Two addition chains
    (+1, +2, +2, ... and +2, +2, ...) keep the dependency chain short."""
    if B < 3:
        for i in range(B):
            emit(f"\tVREV64 V{CTR}.B16, {v(i)}")
            emit(f"\tVADD V{ONE}.D2, V{CTR}.D2, V{CTR}.D2")
        return
    emit(f"\tVADD V{ONE}.D2, V{CTR}.D2, V1.D2")
    emit(f"\tVADD V{TWO}.D2, V{CTR}.D2, V2.D2")
    emit(f"\tVREV64 V{CTR}.B16, V0.B16")
    for k in range(3, B):
        emit(f"\tVADD V{TWO}.D2, V{k-2}.D2, V{k}.D2")
    emit(f"\tVADD V{TWO}.D2, V{B-2}.D2, V{CTR}.D2")
    for k in range(1, B):
        emit(f"\tVREV64 {v(k)}, {v(k)}")


def rounds_and_finish(nr, B, eor3):
    S = min(args.stage, B)
    last = keyreg(nr, nr)
    for k in range(nr - 1):
        for i in range(B):
            emit(f"\tAESE {v(keyreg(nr, k))}, {v(i)}")
            emit(f"\tAESMC {v(i)}, {v(i)}")
    for i in range(B):
        emit(f"\tAESE {v(keyreg(nr, nr - 1))}, {v(i)}")
    pending = []
    for g in range(0, B, S):
        n = min(S, B - g)
        regs = [STAGE0 + j for j in range(n)]
        emit(f"\tVLD1.P {16*n}(SRC), [{', '.join(v(r) for r in regs)}]")
        for j in range(n):
            i = g + j
            if eor3:
                emit(f"\tVEOR3 {v(last)}, {v(regs[j])}, {v(i)}, {v(i)}")
            else:
                emit(f"\tVEOR {v(i)}, {v(last)}, {v(i)}")
                emit(f"\tVEOR {v(i)}, {v(regs[j])}, {v(i)}")
            pending.append(i)
        while len(pending) >= 4 or (g + n == B and pending):
            chunk, pending = pending[:4], pending[4:]
            emit(f"\tVST1.P [{', '.join(v(r) for r in chunk)}], {16*len(chunk)}(DST)")


def function(fname, eor3):
    emit(f"// func {fname}(nr int, xk *[60]uint32, dst, src *byte, n, r int, ivlo, ivhi uint64)")
    emit(f"TEXT ·{fname}(SB), NOSPLIT, $0")
    emit("\tMOVD nr+0(FP), NR")
    emit("\tMOVD xk+8(FP), XK")
    emit("\tMOVD dst+16(FP), DST")
    emit("\tMOVD src+24(FP), SRC")
    emit("\tMOVD n+32(FP), R13")
    emit("\tMOVD r+40(FP), R15")
    emit("\tMOVD ivlo+48(FP), IV_LOW_LE")
    emit("\tMOVD ivhi+56(FP), IV_HIGH_LE")
    emit(f"\tVMOV IV_HIGH_LE, V{CTR}.D[0]")
    emit(f"\tVMOV IV_LOW_LE, V{CTR}.D[1]")
    emit(f"\tVEOR V{ONE}.B16, V{ONE}.B16, V{ONE}.B16")
    emit("\tMOVD $1, R14")
    emit(f"\tVMOV R14, V{ONE}.D[1]")
    emit(f"\tVADD V{ONE}.D2, V{ONE}.D2, V{TWO}.D2")
    emit("\tCMP $12, NR")
    emit("\tBLT Lnr10")
    emit("\tBEQ Lnr12")
    for nr in (14, 12, 10):
        emit(f"Lnr{nr}:")
        load_keys(nr)
        emit(f"\tCBZ R13, Ltail{nr}")
        emit(f"Lloop{nr}:")
        counters(G)
        rounds_and_finish(nr, G, eor3)
        emit("\tSUB $1, R13, R13")
        emit(f"\tCBNZ R13, Lloop{nr}")
        emit(f"Ltail{nr}:")
        for b in (8, 4, 2, 1):
            if b >= G:
                continue
            emit(f"\tAND ${b}, R15, R16")
            emit(f"\tCBZ R16, Lskip{nr}_{b}")
            counters(b)
            rounds_and_finish(nr, b, eor3)
            emit(f"Lskip{nr}_{b}:")
        emit("\tRET")
        emit("")


with open(args.orig) as f:
    emit(f.read().rstrip("\n"))
emit("")
emit(f"// Candidate: blocks={G} stage={args.stage}")
function("ctrBlocksAsm", False)
function("ctrBlocksEOR3Asm", True)
sys.stdout.write("\n".join(out) + "\n")
