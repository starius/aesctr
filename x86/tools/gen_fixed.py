#!/usr/bin/env python3
"""Write AesCtrX86/FRuns.lean: one lemma per fixed-size function of master
(ctrBlocks1Asm, ctrBlocks2Asm, ctrBlocks4Asm, ctrBlocks8Asm), key size and,
for ctrBlocks8Asm, path (PADDQ when the low half of the counter does not wrap
within the 8 blocks, ADDQ/ADCQ otherwise).

Usage: gen_fixed.py <FRuns.lean>

Each lemma runs the whole function, from its entry to RET: the counter blocks,
round 0, the branch on the key size, the rounds, the last round, the XOR with
the source and the stores. A run ends at a taken jump; the next one starts at
its target.
"""
import sys

# name, blocks, entry, R192 label, R128 label, [slow label, join label].
FUNCS = [
    ("1", 1, 0x5421a0, 0x5421ff, 0x542214, None, None),
    ("2", 2, 0x542280, 0x542306, 0x542325, None, None),
    ("4", 4, 0x5423e0, 0x5424b4, 0x5424e7, None, None),
    ("8", 8, 0x542620, 0x5427fb, 0x542858, 0x5426ba, 0x542746),
]
TWO64 = 2 ** 64


def vs(j):
    return " ".join("v%d" % i for i in range(j))


def stores_term(j):
    t = "c.mem"
    for i in range(j):
        t = "(Mem.storeInt %s (blockAddr c.dst %d) 16 v%d)" % (t, i, i)
    return t


def store_list(j):
    return "[" + ", ".join("(%d, v%d)" % (i, i) for i in range(j)) + "]"


def facts(n, nr):
    out = ["have hinv := memInv_zero c",
           "have hb0 : 0 ≤ c.n := Nat.zero_le _",
           "have hmask : Mem.loadInt c.mem 5621904#64 16 = some (maskVal.toNat : Int) := hc.mask"]
    names = ["hmask"]
    for r in range(nr + 1):
        addr = "c.xk" if r == 0 else "(c.xk + BitVec.ofNat 64 %d)" % (16 * r)
        out.append("have k%d : Mem.loadInt c.mem %s 16 = some ((c.rk %d).toNat : Int) := by\n"
                   "    simpa [blockAddr] using key_fact hc.toBufs hinv hb0 %d (by omega)" % (r, addr, r, r))
        names.append("k%d" % r)
    for j in range(n):
        q = "∀ %s : Int, " % vs(j) if j else ""
        lam = "fun %s => " % vs(j) if j else ""
        out.append("have s%d : %sMem.loadInt %s (blockAddr c.src %d) 16 =\n"
                   "      some ((c.srcb %d).toNat : Int) :=\n"
                   "    %ssrc_fact hc.toBufs hinv %d (by omega) (by omega) %s (by simp; try omega)"
                   % (j, q, stores_term(j), j, j, lam, j, store_list(j)))
        out.append("obtain ⟨z%d, hz%d⟩ := hc.dsts %d (by omega)" % (j, j, j))
        out.append("have d%d : %sMem.loadInt %s (blockAddr c.dst %d) 16 = some z%d :=\n"
                   "    %s(dst_fact hc.toBufs hinv %d (by omega) (by omega) %s (by simp; try omega)).trans hz%d"
                   % (j, q, stores_term(j), j, j, lam, j, store_list(j), j))
        names += ["s%d" % j, "d%d" % j]
    out.append("have hra : ∀ %s : Int, Mem.loadInt %s c.rsp 8 = some (c.ra.toNat : Int) :=\n"
               "    fun %s => ra_fact hc %s (by simp; omega)" % (vs(n), stores_term(n), vs(n), store_list(n)))
    names.append("hra")
    return out, names


def mem_proof(n, fast):
    lines = []
    for j in reversed(range(n)):
        lines.append("refine memInv_store' hc.toBufs (b := %d) (by omega) ?m%d (by omega) _ ?v%d" % (j, j, j))
        lines.append("case v%d =>" % j)
        if j == 0:
            lines.append("  rw [← out_std c 0 (c.ivhi ++ c.ivlo) (by simp)]")
        elif fast:
            lines.append("  rw [← out_fast c %d (by omega)]" % j)
        else:
            lines.append("  rw [← out_std c %d _ rfl]" % j)
        lines.append("  simp only [hnr, encRounds, maskVal, Nat.reduceAdd, Nat.reduceSub]")
    lines.append("exact hinv")
    return ["  " + l for l in lines]


def lemma(f, nr, path):
    name, n, entry, r192, r128, slow, join = f
    fs, fnames = facts(n, nr)
    blocks = [r192, r128] + ([slow, join] if slow else [])
    blk = ", ".join("next_%x, blk_%x, label_%x" % (a, a, a) for a in blocks)
    lemmas = ("hrsp, hc.arg_nr, hc.arg_xk, arg_dst0 hc, arg_src0 hc, arg_lo hc, arg_hi hc, ctr_lanes', "
              "hnr, ofInt_natCast64, hi64_append_lo64, add_lo64, adc_hi64, add_ofNat_ofNat128, "
              "addFlags_cf7, incFlags_fst, BitVec.xor_self, pinsrq_lo, Int64.reduceSub, "
              "Int64.ofBitVec_toBitVec, RelRegOrMem.interp, ofBitVec_ofNat64")
    if path:
        lemmas += ", hw"
    step = "xstep [%s, %s, %s]" % (lemmas, ", ".join(fnames), blk)
    # The runs: each starts at the target of the jump that ended the one before.
    starts = []
    if path == "slow":
        starts.append(slow)
    elif path == "fast":
        starts.append(join)
    if nr == 12:
        starts.append(r192)
    elif nr == 10:
        starts.append(r128)
    if path is None:
        hw, doc = "", ""
    elif path == "fast":
        hw = "\n    (hw : ¬ %d ≤ 7 + (lo64 (c.ivhi ++ c.ivlo)).toNat)" % TWO64
        doc = ", when the low 64 bits of the counter do not wrap within the\n8 blocks (PADDQ)"
    else:
        hw = "\n    (hw : %d ≤ 7 + (lo64 (c.ivhi ++ c.ivlo)).toNat)" % TWO64
        doc = ", when the low 64 bits of the counter wrap within the 8 blocks\n(ADDQ and ADCQ)"
    L = ["""/-- `ctrBlocks%(name)sAsm`, AES-%(bits)d%(doc)s: it returns with block `j < %(n)d`
of `dst` holding block `j` of `src` XOR keystream block `j`. -/
theorem f%(name)s_%(nr)d%(suffix)s (c : Call) (hc : PreF c) (hn : c.n = %(n)d) (hnr : c.nr = %(nr)d)
    (hrsp : c.regs.rsp.toBitVec = c.rsp) (zmms : RegZmms) (flags : StatusFlags)%(hw)s :
    Runs exe (Post c) (⟨c.regs, zmms, flags, c.mem⟩, 0x%(entry)x) := by""" % dict(
        name=name, n=n, nr=nr, bits={10: 128, 12: 192, 14: 256}[nr], doc=doc,
        suffix="_" + path if path else "", hw=hw, entry=entry)]
    if path == "fast":
        L.append("  have hlo : c.ivlo.toNat + 7 < 2 ^ 64 := by\n"
                 "    have h := hw\n    rw [lo64_append] at h\n    omega")
    for x in fs:
        L.append("  " + x)
    L.append("  rw [runs_def, next_%x]" % entry)
    L.append("  simp only [blk_%x]" % entry)
    L.append("  " + step)
    L.append("  intros")
    for _ in starts:
        L.append("  apply reaches_of_runs")
        L.append("  rw [runs_def]")
        L.append("  " + step)
        L.append("  intros")
    L.append("  refine reaches_done ⟨by simp, by simp [hrsp], rfl, rfl, rfl, ?_⟩")
    L.append("  rw [hn]")
    L += mem_proof(n, path == "fast")
    return "\n".join(L) + "\n"


def main():
    out = ["""/-
Generated by gen_fixed.py: do not edit.

Runs of master's fixed-size functions, one lemma per function, key size and,
for ctrBlocks8Asm, path.
-/
import AesCtrX86.FLemmas

open Std Std.ExtHashMap

namespace AesCtrX86

set_option maxHeartbeats 40000000
set_option maxRecDepth 200000
"""]
    for f in FUNCS:
        for path in (["fast", "slow"] if f[5] else [None]):
            for nr in (10, 12, 14):
                out.append(lemma(f, nr, path))
    out.append("end AesCtrX86\n")
    open(sys.argv[1], "w").write("\n".join(out))


main()
