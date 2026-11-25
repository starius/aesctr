#!/usr/bin/env python3
"""Round-2 experimental arm64 AES-CTR variants (Go assembler syntax).

Usage: gen_ctr_asm2.py [options] <original ctr_arm64.s> > ctr_arm64.s

Appends to the original file

  func ctrBlocksLoopAsm(nr int, xk *[60]uint32, dst, src *byte, n, r int, ivlo, ivhi uint64)

which XORs n groups of G blocks and then r < G more blocks (with --tail asm;
otherwise r must be 0) of keystream into dst. The low 64 bits of the counter
must not wrap inside the call (the Go caller splits there).
"""
import argparse
import sys

p = argparse.ArgumentParser()
p.add_argument("orig")
p.add_argument("--blocks", type=int, default=8)
p.add_argument("--eor3", action="store_true")
p.add_argument("--stage", type=int, default=4)
p.add_argument("--chain", type=int, default=1, help="counter chains (1 or 2)")
p.add_argument("--early", type=int, default=0, help="issue the first plaintext load this many rounds early")
p.add_argument("--tail", choices=["none", "asm"], default="none")
args = p.parse_args()

G = args.blocks
NKEYS = 15
KEND = G + NKEYS - 1
STAGE0 = KEND + 1
CTR = STAGE0 + args.stage
ONE = CTR + 1
TWO = ONE + 1 if args.chain == 2 else None
assert (TWO or ONE) <= 31, "register budget"

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
    """Counter blocks for B blocks into V0..V(B-1); CTR advances by B."""
    if args.chain == 1 or B < 3:
        for i in range(B):
            emit(f"\tVREV64 V{CTR}.B16, {v(i)}")
            emit(f"\tVADD V{ONE}.D2, V{CTR}.D2, V{CTR}.D2")
        return
    # Two chains: V1 = C+1, V2 = C+2, Vk = V(k-2) + 2; native values first,
    # byte-reversed in place once their dependants exist.
    emit(f"\tVADD V{ONE}.D2, V{CTR}.D2, V1.D2")
    emit(f"\tVADD V{TWO}.D2, V{CTR}.D2, V2.D2")
    emit(f"\tVREV64 V{CTR}.B16, V0.B16")
    for k in range(3, B):
        emit(f"\tVADD V{TWO}.D2, V{k-2}.D2, V{k}.D2")
    # next counter: C + B = V(B-2) + 2
    emit(f"\tVADD V{TWO}.D2, V{B-2}.D2, V{CTR}.D2")
    for k in range(1, B):
        emit(f"\tVREV64 {v(k)}, {v(k)}")


def rounds_and_finish(nr, B):
    """AES rounds for V0..V(B-1), then XOR with the last key and plaintext, store."""
    S = min(args.stage, B)
    last = keyreg(nr, nr)
    early_at = (nr - 1) - args.early if args.early else None  # round index after which to load
    first_loaded = False

    def first_load():
        n = S
        regs = [STAGE0 + j for j in range(n)]
        emit(f"\tVLD1.P {16*n}(SRC), [{', '.join(v(r) for r in regs)}]")

    for k in range(nr - 1):
        for i in range(B):
            emit(f"\tAESE {v(keyreg(nr, k))}, {v(i)}")
            emit(f"\tAESMC {v(i)}, {v(i)}")
        if early_at is not None and k + 1 == early_at and not first_loaded:
            first_load()
            first_loaded = True
    for i in range(B):
        emit(f"\tAESE {v(keyreg(nr, nr - 1))}, {v(i)}")
    # Output = state ^ last ^ plaintext, written into the state registers.
    pending = []
    for g in range(0, B, S):
        n = min(S, B - g)
        regs = [STAGE0 + j for j in range(n)]
        if not (g == 0 and first_loaded):
            emit(f"\tVLD1.P {16*n}(SRC), [{', '.join(v(r) for r in regs)}]")
        for j in range(n):
            i = g + j
            if args.eor3:
                emit(f"\tVEOR3 {v(last)}, {v(regs[j])}, {v(i)}, {v(i)}")
            else:
                emit(f"\tVEOR {v(i)}, {v(last)}, {v(i)}")
                emit(f"\tVEOR {v(i)}, {v(regs[j])}, {v(i)}")
            pending.append(i)
        while len(pending) >= 4 or (g + n == B and pending):
            chunk, pending = pending[:4], pending[4:]
            emit(f"\tVST1.P [{', '.join(v(r) for r in chunk)}], {16*len(chunk)}(DST)")


with open(args.orig) as f:
    emit(f.read().rstrip("\n"))
emit("")
emit(f"// Experimental: blocks={G} eor3={args.eor3} stage={args.stage} chain={args.chain} early={args.early} tail={args.tail}")
emit("// func ctrBlocksLoopAsm(nr int, xk *[60]uint32, dst, src *byte, n, r int, ivlo, ivhi uint64)")
emit("TEXT ·ctrBlocksLoopAsm(SB), NOSPLIT, $0")
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
if TWO:
    emit(f"\tVADD V{ONE}.D2, V{ONE}.D2, V{TWO}.D2")
emit("\tCMP $12, NR")
emit("\tBLT Lnr10")
emit("\tBEQ Lnr12")
for nr, label in ((14, "14"), (12, "12"), (10, "10")):
    emit(f"Lnr{label}:")
    load_keys(nr)
    emit(f"\tCBZ R13, Ltail{label}")
    emit(f"Lloop{label}:")
    counters(G)
    rounds_and_finish(nr, G)
    emit("\tSUB $1, R13, R13")
    emit(f"\tCBNZ R13, Lloop{label}")
    emit(f"Ltail{label}:")
    if args.tail == "asm":
        bits = [b for b in (8, 4, 2, 1) if b < G]
        for b in bits:
            emit(f"\tAND ${b}, R15, R16")
            emit(f"\tCBZ R16, Lskip{label}_{b}")
            counters(b)
            rounds_and_finish(nr, b)
            emit(f"Lskip{label}_{b}:")
    emit("\tRET")
    emit("")

sys.stdout.write("\n".join(out) + "\n")
