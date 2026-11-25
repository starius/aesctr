#!/usr/bin/env python3
"""Generate the group lemmas of the bulk function's proof (efficient form).

Usage: gen_bulk_proof2.py <program.lean> <namespace> <prog> <layout> <keyEnd>
           <ctr,one,two> <out.lean> <group>...

A <group> is `name:nr:start:end:B`: the straight-line code [start, end)
processes B blocks for nr rounds. Its lemma: from a state at `start`
satisfying `LoopInv layout s0 c m`, the code reaches `end` satisfying
`LoopInv ... (m + B)` (`GroupPost`).

The proof keeps terms small. After `sym_n`, it first proves facts about
intermediate states: the pointer registers before each store, and that each
loaded plaintext register holds the initial source block. Then one lemma per
output block gives the stored register's value in terms of the spec, and
memory reads of the final state resolve against stores of those registers.
The generator only proposes text; Lean checks every step.
"""
import re
import sys


def parse_program(path):
    insts = []
    for line in open(path):
        m = re.match(r"\s*\[?\((0x[0-9a-f]+)#64, (0x[0-9a-f]+)#32\)[,\]]*\s*--\s*(.*?)\s*\|", line)
        if m:
            insts.append((int(m.group(1), 16), int(m.group(2), 16), m.group(3).strip()))
    return insts


def parse_ldst(text):
    """(kind, regs, base, post) for `ld1/st1 { vN.16b, ... }, [xB], #P`, else None."""
    m = re.match(r"(ld1|st1)\s+\{ ([^}]*) \}, \[x(\d+)\], #(\d+)$", text)
    if not m:
        return None
    regs = [int(r) for r in re.findall(r"v(\d+)\.16b", m.group(2))]
    return m.group(1), regs, int(m.group(3)), int(m.group(4))


def st(p):
    """Name of the state before position p of the group (s, s1, s2, ...)."""
    return "s" if p == 0 else f"s{p}"


def group_lemma(prog, layout, keyEnd, regs, insts, name, nr, start, end, B):
    CTR, ONE, TWO = regs
    body = [(a, w, t) for (a, w, t) in insts if start <= a < end]
    n = len(body)
    assert n == (end - start) // 4
    memfx = ", ".join(f"h_s{k}_memory_effects" for k in range(n, 0, -1))
    L = []
    A = L.append
    A(f"""
theorem {name} (s0 s sf : ArmState) (c : Call) (m : Nat)
    (hinv : LoopInv {layout} s0 c m s) (h_nr : c.nr = {nr})
    (h_s_pc : r .PC s = 0x{start:x}#64)
    (h_fit : m + {B} ≤ c.nblocks) (h_nowrap : c.ivlo.toNat + c.nblocks ≤ 2 ^ 64)
    (h_dst : c.dst.toNat + 16 * c.nblocks ≤ 2 ^ 64)
    (h_src : c.src.toNat = c.dst.toNat ∨ c.src.toNat + 16 * c.nblocks ≤ c.dst.toNat ∨
      c.dst.toNat + 16 * c.nblocks ≤ c.src.toNat)
    (h_src_legal : c.src.toNat + 16 * c.nblocks ≤ 2 ^ 64)
    (h_run : sf = run {n} s) :
    GroupPost {layout} s0 c (m + {B}) 0x{end:x}#64 (r (.GPR 13#5) s) sf := by
  obtain ⟨h_s_program, h_s_err, h_s_sp_aligned, hsp, h18, h28, h29, h30, hkeys, hone, htwo, hctr,
    hsrcp, hdstp, hrem, hdone, hframe⟩ := hinv
  replace h_s_program : s.program = {prog} := h_s_program
  replace hone : r (.SFP {ONE}#5) s = 1#64 ++ 0#64 := hone
  replace htwo : r (.SFP {TWO}#5) s = 2#64 ++ 0#64 := htwo
  replace hctr : r (.SFP {CTR}#5) s = (c.ivlo + BitVec.ofNat 64 m) ++ c.ivhi := hctr""")
    for k in range(nr + 1):
        A(f"""  have hk{k} : r (.SFP {keyEnd - nr + k}#5) s = block s0 c.xk {k} := by
    have := hkeys {k} (by rw [h_nr]; omega)
    rw [h_nr] at this
    exact this""")
    A("""  have hframe' : ∀ (a : BitVec 64) (k : Nat), mem_separate' a k c.dst (16 * m) →
      Memory.read_bytes k a s.mem = Memory.read_bytes k a s0.mem := by
    intro a k h
    have := hframe a k h
    simpa only [Memory.State.read_mem_bytes_eq_mem_read_bytes] using this""")
    A(f"  sym_n {n}")
    keyrw = ", ".join(f"hk{k}" for k in range(nr + 1))
    # Pointer facts before each load and store, and the stores' contents.
    src_off = 0   # bytes the source pointer has advanced within the group
    dst_off = 0
    stores = []   # (p, regs, dst_off)
    loads = []    # (p, regs, src_off)
    for p, (a, w, t) in enumerate(body):
        ls = parse_ldst(t)
        if not ls:
            continue
        kind, rs, base, post = ls
        if kind == "ld1":
            assert base == 12, t
            loads.append((p, rs, src_off))
            src_off += post
        else:
            assert base == 11, t
            stores.append((p, rs, dst_off))
            dst_off += post
    assert src_off == 16 * B and dst_off == 16 * B, (src_off, dst_off)
    for (p, rs, off) in stores:
        A(f"""  have hx11_{p} : r (.GPR 11#5) {st(p)} = c.dst + (BitVec.ofNat 64 (16 * m) + {off}#64) := by
    sym_aggregate
    try simp only [hdstp, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]""")
    # Memory of state s{p}: writes of the stores before p over s.mem.
    for (p, rs, off) in loads:
        A(f"""  have hx12_{p} : r (.GPR 12#5) {st(p)} = c.src + (BitVec.ofNat 64 (16 * m) + {off}#64) := by
    sym_aggregate
    try simp only [hsrcp, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]""")
        fx = ", ".join(f"h_s{k}_memory_effects" for k in range(p, 0, -1))
        xs = ", ".join(f"hx11_{q}" for (q, _, _) in stores if q < p)
        for j, q in enumerate(rs):
            A(f"""  have hld_{p}_{q} : r (.SFP {q}#5) s{p + 1} =
      Memory.read_bytes 16 (c.src + (BitVec.ofNat 64 (16 * m) + {off + 16 * j}#64)) s0.mem := by
    rw [h_s{p + 1}_q{q}]
    simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes, hx12_{p}, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.add_zero{', ' + fx if fx else ''}{', write_mem_bytes_mem' if xs else ''}{', ' + xs if xs else ''}]
    simp (disch := no_recover mem_tac) only [rd_write_sep, hframe', BitVec.add_assoc, BitVec.reduceAdd]""")
            A(f"  clear h_s{p + 1}_q{q}")
    # Value of each stored block. The last step puts the XOR of the plaintext,
    # the AES state and the last round key in the spec's order: two EORs give
    # src ^^^ (key ^^^ state), EOR3 gives (src ^^^ state) ^^^ key. (xor_plain
    # also rewrites the EOR3 goal without closing it, so EOR3 groups skip it.)
    if any(t.split()[0] == "eor3" for (_, _, t) in body):
        xorfin = "rw [xor_eor3]"
    else:
        xorfin = "first | rw [xor_plain] | rw [xor_eor3]"
    for (p, rs, off) in stores:
        for j, q in enumerate(rs):
            k = off // 16 + j
            A(f"""  have hval_{p}_{q} : r (.SFP {q}#5) {st(p)} =
      block s0 c.src (m + {k}) ^^^ keystream c.nr (block s0 c.xk) c.ivhi c.ivlo (m + {k}) := by
    sym_aggregate
    simp only [{keyrw}, hctr, hone, htwo, vadd2d_append, vadd2d_one, vadd2d_two, vrev128_64_8_append, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.add_zero]
    rw [keystream, ctr_nocarry _ _ _ (by omega), counterBlock_append, h_nr]
    simp only [aesEncrypt, aesState, block, subBytes_shiftRows, SubBytes, ShiftRows, MixColumns,
      ofNat_add_64, mul_add_ofNat_64, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.add_zero, BitVec.ofNat_eq_ofNat, Memory.State.read_mem_bytes_eq_mem_read_bytes]
    {xorfin}""")
    A(GROUP_TAIL.format(n=n, layout=layout, memfx=memfx, nr=nr, B=B,
        xs=", ".join(f"hx11_{p}" for (p, _, _) in stores),
        kcases=" ∨ ".join(f"k = {k}" for k in range(nr + 1)),
        krfl=" | ".join("rfl" for _ in range(nr + 1)),
        kcase="\n".join(f"    · rw [h_nr]\n      simp only [Layout.keyReg, {layout}, Nat.reduceSub, Nat.reduceAdd]\n      sym_aggregate <;> exact hk{k}" for k in range(nr + 1)),
        jcases=" ∨ ".join(f"k = {k}" for k in range(B)),
        jrfl=" | ".join("rfl" for _ in range(B)),
        jcase="\n".join(f"      · simp only [mul_add_ofNat_64, Nat.reduceMul, BitVec.add_zero]\n        simp (disch := no_recover mem_tac) only [rd16_write_same, rd_write_sep]\n        exact hval_{p}_{q}" for (p, rs, off) in stores for (j, q) in enumerate(rs))))
    return "\n".join(L)


def main():
    prog_path, ns, prog, layout, keyEnd, regs, out_path = sys.argv[1:8]
    keyEnd = int(keyEnd)
    regs = tuple(int(x) for x in regs.split(","))
    insts = parse_program(prog_path)
    mod = prog_path.split("lean/")[-1].removesuffix(".lean").replace("/", ".")
    L = ["/- Generated by tools/gen_bulk_proof2.py; do not edit. -/",
         "import Tactics.Sym", "import Tactics.StepThms", "import Tactics.Aggregate",
         "import AesCtr.Loop", f"import {mod}", f"import {mod}Layout", f"import {mod}Steps", "", f"namespace {ns}", "open AesCtr", "",
         "set_option maxRecDepth 100000", "set_option maxHeartbeats 0",
         "set_option linter.unusedVariables false", ""]
    for g in sys.argv[8:]:
        name, nr, start, end, B = g.split(":")
        L.append(group_lemma(prog, layout, keyEnd, regs, insts, name, int(nr), int(start, 16),
                             int(end, 16), int(B)))
    L.append(f"end {ns}")
    with open(out_path, "w") as f:
        f.write("\n".join(L) + "\n")


GROUP_TAIL = """  refine ⟨⟨h_s{n}_program, h_s{n}_err, h_s{n}_sp_aligned, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩, h_s{n}_pc, ?_⟩
  · sym_aggregate <;> exact hsp
  · sym_aggregate <;> exact h18
  · sym_aggregate <;> exact h28
  · sym_aggregate <;> exact h29
  · sym_aggregate <;> exact h30
  · intro k hk
    rw [h_nr] at hk
    have : {kcases} := by omega
    rcases this with {krfl}
{kcase}
  · simp only [{layout}]
    sym_aggregate <;> exact hone
  · simp only [{layout}]
    sym_aggregate <;> exact htwo
  · simp only [{layout}]
    sym_aggregate
    try simp only [hctr, hone, htwo, vadd2d_append, vadd2d_one, vadd2d_two, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero,
      ofNat_add_64]
  · sym_aggregate
    try simp only [hsrcp, BitVec.add_assoc, BitVec.reduceAdd, mul_add_ofNat_64, Nat.reduceMul]
  · sym_aggregate
    try simp only [hdstp, BitVec.add_assoc, BitVec.reduceAdd, mul_add_ofNat_64, Nat.reduceMul]
  · sym_aggregate <;> exact hrem
  · intro j hj
    rw [show block s{n} c.dst j = Memory.read_bytes 16 (c.dst + BitVec.ofNat 64 (16 * j)) s{n}.mem by
      simp only [block, Memory.State.read_mem_bytes_eq_mem_read_bytes]]
    simp only [{memfx}, write_mem_bytes_mem]
    simp only [{xs}, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
    by_cases hjm : j < m
    · simp (disch := no_recover mem_tac) only [rd_write_sep]
      have := hdone j hjm
      simpa only [block, Memory.State.read_mem_bytes_eq_mem_read_bytes] using this
    · obtain ⟨k, rfl⟩ : ∃ k, j = m + k := ⟨j - m, by omega⟩
      have : {jcases} := by omega
      rcases this with {jrfl}
{jcase}
  · intro a k hsep
    simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes]
    simp only [{memfx}, write_mem_bytes_mem]
    simp only [{xs}, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
    obtain ⟨h_a_legal, -, h_a_sep⟩ := hsep.omega_def
    simp (disch := no_recover mem_tac) only [rd_write_sep]
    apply hframe'
    mem_tac
  · sym_aggregate"""


if __name__ == "__main__":
    main()
