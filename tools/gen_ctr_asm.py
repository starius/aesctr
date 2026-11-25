#!/usr/bin/env python3
"""Generate experimental arm64 AES-CTR loop variants (Go assembler syntax).

Usage: gen_ctr_asm.py [options] <original ctr_arm64.s> > ctr_arm64.s

Keeps the original ctrBlocks{1,2,4,8}Asm functions and appends

    func ctrBlocks8LoopAsm(nr int, xk *[60]uint32, dst, src *byte, n int, ivlo, ivhi uint64)

which XORs n groups of B blocks (B = --blocks) of keystream into dst. The low
64 bits of the counter must not wrap inside the call (the Go caller splits
there), except with --ctr ins, which carries like the original code.
"""
import argparse
import sys

p = argparse.ArgumentParser()
p.add_argument("orig")
p.add_argument("--blocks", type=int, default=8)
p.add_argument("--ctr", choices=["vec64", "ins"], default="vec64")
p.add_argument("--eor3", action="store_true")
p.add_argument("--stage", type=int, default=4, help="plaintext staging registers")
args = p.parse_args()

B = args.blocks
NKEYS = 15
# Register plan: blocks V0..V(B-1); keys end at KEND; then staging, CTR, ONE.
KEND = B + NKEYS - 1          # last key register
STAGE0 = KEND + 1
CTR = STAGE0 + args.stage
ONE = CTR + 1
assert ONE <= 31, (B, args.stage, ONE)

out = []
emit = out.append


def v(i):
    return f"V{i}.B16"


def keyreg(nr, k):
    """Register holding round key k (0..nr) for nr rounds."""
    return KEND - nr + k


def load_keys(nr):
    first = keyreg(nr, 0)
    regs = list(range(first, KEND + 1))
    while regs:
        chunk, regs = regs[:4], regs[4:]
        emit(f"\tVLD1.P {16*len(chunk)}(XK), [{', '.join(v(r) for r in chunk)}]")


def counters():
    if args.ctr == "vec64":
        for i in range(B):
            emit(f"\tVREV64 V{CTR}.B16, {v(i)}")
            emit(f"\tVADD V{ONE}.D2, V{CTR}.D2, V{CTR}.D2")
    else:
        for i in range(B):
            emit("\tREV IV_LOW_LE, IV_LOW_BE")
            emit("\tREV IV_HIGH_LE, IV_HIGH_BE")
            emit(f"\tVMOV IV_LOW_BE, V{i}.D[1]")
            emit(f"\tVMOV IV_HIGH_BE, V{i}.D[0]")
            emit("\tADDS $1, IV_LOW_LE")
            emit("\tADC $0, IV_HIGH_LE")


def rounds(nr):
    for k in range(nr - 1):
        for i in range(B):
            emit(f"\tAESE {v(keyreg(nr, k))}, {v(i)}")
            emit(f"\tAESMC {v(i)}, {v(i)}")
    for i in range(B):
        emit(f"\tAESE {v(keyreg(nr, nr - 1))}, {v(i)}")


def finish(nr):
    last = keyreg(nr, nr)
    S = args.stage
    if not args.eor3:
        for i in range(B):
            emit(f"\tVEOR {v(i)}, {v(last)}, {v(i)}")
    for g in range(0, B, S):
        n = min(S, B - g)
        regs = [STAGE0 + j for j in range(n)]
        emit(f"\tVLD1.P {16*n}(SRC), [{', '.join(v(r) for r in regs)}]")
        for j in range(n):
            if args.eor3:
                emit(f"\tVEOR3 {v(last)}, {v(g + j)}, {v(regs[j])}, {v(regs[j])}")
            else:
                emit(f"\tVEOR {v(g + j)}, {v(regs[j])}, {v(regs[j])}")
        emit(f"\tVST1.P [{', '.join(v(r) for r in regs)}], {16*n}(DST)")


with open(args.orig) as f:
    orig = f.read()
emit(orig.rstrip("\n"))
emit("")
emit(f"// Experimental variant: blocks={B} ctr={args.ctr} eor3={args.eor3} stage={args.stage}")
emit("// func ctrBlocks8LoopAsm(nr int, xk *[60]uint32, dst, src *byte, n int, ivlo, ivhi uint64)")
emit("TEXT ·ctrBlocks8LoopAsm(SB), NOSPLIT, $0")
emit("\tMOVD nr+0(FP), NR")
emit("\tMOVD xk+8(FP), XK")
emit("\tMOVD dst+16(FP), DST")
emit("\tMOVD src+24(FP), SRC")
emit("\tMOVD n+32(FP), R13")
emit("\tMOVD ivlo+40(FP), IV_LOW_LE")
emit("\tMOVD ivhi+48(FP), IV_HIGH_LE")
if args.ctr == "vec64":
    emit(f"\tVMOV IV_HIGH_LE, V{CTR}.D[0]")
    emit(f"\tVMOV IV_LOW_LE, V{CTR}.D[1]")
    emit(f"\tVEOR V{ONE}.B16, V{ONE}.B16, V{ONE}.B16")
    emit("\tMOVD $1, R14")
    emit(f"\tVMOV R14, V{ONE}.D[1]")
emit("\tCMP $12, NR")
emit("\tBLT Lloop128")
emit("\tBEQ Lloop192")
for nr, label in ((14, "256"), (12, "192"), (10, "128")):
    emit(f"Lloop{label}:")
    load_keys(nr)
    emit(f"Lgroup{label}:")
    counters()
    rounds(nr)
    finish(nr)
    emit("\tSUBS $1, R13, R13")
    emit(f"\tBNE Lgroup{label}")
    emit("\tRET")
    emit("")

sys.stdout.write("\n".join(out) + "\n")
