#!/usr/bin/env python3
"""Generate the control-flow part of the bulk function's proof.

Usage: gen_bulk_ctl.py <program.lean> <ns> <prog> <layout> <prefix> <outdir>

Reads the program, finds its structure (nr dispatch, key loads, loop, tail
steps), and writes:
  <outdir>/<Prefix>Groups.txt   group lemma arguments for gen_bulk_proof2.py
  <outdir>/<Prefix>Ctl.lean     for each nr: prologue, branch steps and return
                                (gen_bulk_main.py composes them).
The generator only proposes text; Lean checks it.
"""
import re
import sys

G = 12


def parse_program(path):
    insts = []
    for line in open(path):
        m = re.match(r"\s*\[?\((0x[0-9a-f]+)#64, (0x[0-9a-f]+)#32\)[,\]]*\s*--\s*(.*?)\s*\|", line)
        if m:
            insts.append((int(m.group(1), 16), int(m.group(2), 16), m.group(3).strip()))
    return insts


def sext(v, bits):
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


def br_target(addr, word):
    return addr + sext((word >> 5) & 0x7ffff, 19) * 4


def analyse(insts):
    code = {a: (w, t) for a, w, t in insts}
    addrs = [a for a, _, _ in insts]
    first = {}
    for a, w, t in insts:
        op = t.split()[0]
        first.setdefault(op, (a, w))
    blt_a, blt_w = first["b.lt"]
    beq_a, beq_w = first["b.eq"]
    starts = {14: beq_a + 4, 12: br_target(beq_a, beq_w), 10: br_target(blt_a, blt_w)}
    secs = {}
    for nr, S in starts.items():
        a = S
        keys = []
        while code[a][1].startswith("ld1"):
            keys.append(a)
            a += 4
        assert code[a][1].startswith("cbz x13"), (hex(a), code[a])
        cbz = a
        tail = br_target(cbz, code[cbz][0])
        loop = cbz + 4
        a = loop
        while not code[a][1].startswith("sub x13"):
            a += 4
        sub = a
        assert code[sub + 4][1].startswith("cbnz x13") and br_target(sub + 4, code[sub + 4][0]) == loop
        assert sub + 8 == tail
        tests = []
        a = tail
        for b in (8, 4, 2, 1):
            assert code[a][1].startswith(f"and x16, x15, #0x{b:x}"), (hex(a), code[a])
            assert code[a + 4][1].startswith("cbz x16")
            skip = br_target(a + 4, code[a + 4][0])
            tests.append((b, a, a + 8, skip))
            a = skip
        assert code[a][1] == "ret", (hex(a), code[a])
        secs[nr] = dict(S=S, keys=keys, cbz=cbz, loop=loop, sub=sub, tail=tail, tests=tests, ret=a)
    return dict(blt=blt_a, beq=beq_a, secs=secs)


def glue(prog, k, addr, nxt):
    p, s = f"s{k-1}", f"s{k}"
    return f"""  init_next_step h_run stepi_{p} {s}
  have h_step_{k} : {s} = w .PC 0x{nxt:x}#64 {p} := by
    have h := stepi_{p}.symm.trans
      ({prog}.stepi_eq_0x{addr:x} h_{p}_program h_{p}_pc h_{p}_err)
    sym_aggregate at h
    exact h
  have h_{s}_program : {s}.program = {prog} := by rw [h_step_{k}, w_program, h_{p}_program]
  have h_{s}_pc : r .PC {s} = 0x{nxt:x}#64 := by rw [h_step_{k}, r_of_w_same]
  have h_{s}_err : r .ERR {s} = .None := by rw [h_step_{k}, r_of_w_different (by decide), h_{p}_err]
  have h_{s}_sp_aligned : CheckSPAlignment {s} := by
    simp only [CheckSPAlignment, read_gpr, h_step_{k},
      r_of_w_different (show StateField.GPR 31#5 ≠ StateField.PC by decide)]
    exact h_{p}_sp_aligned
  have h_{s}_non_effects : ∀ (f : StateField), f ≠ StateField.PC → r f {s} = r f {p} := by
    intro f hf; rw [h_step_{k}, r_of_w_different hf]
  have h_{s}_memory_effects : {s}.mem = {p}.mem := by rw [h_step_{k}]; exact mem_w_of_mem_eq rfl _ _
  clear h_step_{k} stepi_{p}"""


def prologue(A, prog, layout, P, nr, sec, keyEnd):
    """Lemma: from the entry state to the loop-entry CBZ with LoopInv 0."""
    # Path: [0, blt) straight, blt, (beq), key loads.
    pre = A["blt"] // 4               # instructions before b.lt
    steps = []                         # list of ("sym", count) / ("br", addr, target)
    steps.append(("sym", pre))
    if nr == 10:
        steps.append(("br", A["blt"], sec["S"]))
    else:
        steps.append(("br", A["blt"], A["blt"] + 4))
        steps.append(("br", A["beq"], sec["S"]))
    steps.append(("sym", len(sec["keys"])))
    T = sum(s[1] if s[0] == "sym" else 1 for s in steps)
    L = []
    a = L.append
    a(f"""
theorem {P}_pro{nr} (s0 sf : ArmState) (h : Pre {prog} 8 (callBulk {G} s0) s0)
    (h_nr : read_mem_bytes 8 (r (StateField.GPR 31#5) s0 + 8#64) s0 = {nr}#64)
    (h_run : sf = run {T} s0) :
    GroupPost {layout} s0 (callBulk {G} s0) 0 0x{sec['cbz']:x}#64 (arg s0 4) sf := by
  obtain ⟨h_s0_program, h_s0_pc, h_s0_err, h_s0_sp_aligned, -, -, -, -⟩ := h""")
    k = 0
    for st in steps:
        if st[0] == "sym":
            a(f"  sym_n {st[1]}" + (f" at s{k}" if k else ""))
            k += st[1]
        else:
            a(glue(prog, k + 1, st[1], st[2]))
            k += 1
    assert k == T
    memfx = ", ".join(f"h_s{j}_memory_effects" for j in range(T, 0, -1))
    kc = " ∨ ".join(f"k = {j}" for j in range(nr + 1))
    kr = " | ".join("rfl" for _ in range(nr + 1))
    a(f"""  have h_nr' : (callBulk {G} s0).nr = {nr} := by
    simp only [callBulk, arg, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, h_nr]; rfl
  refine ⟨⟨h_s{T}_program, h_s{T}_err, h_s{T}_sp_aligned, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩, h_s{T}_pc, ?_⟩
  · sym_aggregate
  · sym_aggregate
  · sym_aggregate
  · sym_aggregate
  · sym_aggregate
  · intro k hk
    rw [h_nr'] at hk ⊢
    have : {kc} := by omega
    rcases this with {kr}
    all_goals
      simp only [Layout.keyReg, {layout}, Nat.reduceSub, Nat.reduceAdd, callBulk, arg, block,
        Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
      sym_aggregate
      try simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes, {memfx}, BitVec.add_assoc,
        BitVec.reduceAdd]
  · simp only [{layout}]
    sym_aggregate
    try simp only [partInstall_one]
    try decide
  · simp only [{layout}]
    sym_aggregate
    try simp only [partInstall_one, vadd2d_append, BitVec.reduceAdd, BitVec.add_zero]
    try decide
  · simp only [{layout}, callBulk, arg, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat,
      BitVec.add_zero]
    sym_aggregate
    try simp only [partInstall_hi_lo, Memory.State.read_mem_bytes_eq_mem_read_bytes, {memfx}]
  · simp only [callBulk, arg, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    sym_aggregate
    try simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes, {memfx}]
  · simp only [callBulk, arg, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    sym_aggregate
    try simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes, {memfx}]
  · simp only [arg, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
    sym_aggregate
    try simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes, {memfx}]
  · intro j hj; omega
  · intro a k _
    simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes, {memfx}]
  · simp only [arg, Nat.reduceMul, Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
    sym_aggregate
    try simp only [Memory.State.read_mem_bytes_eq_mem_read_bytes, {memfx}]""")
    return "\n".join(L), T


def ctl_lemmas(prog, layout, P, nr, sec):
    L = []
    a = L.append
    cbz, loop, sub, tail, ret = sec["cbz"], sec["loop"], sec["sub"], sec["tail"], sec["ret"]
    a(f"""
theorem {P}_cbz{nr} {{s0 s : ArmState}} {{c : Call}} {{x : BitVec 64}}
    (hg : GroupPost {layout} s0 c 0 0x{cbz:x}#64 x s) :
    GroupPost {layout} s0 c 0 (if x = 0#64 then 0x{tail:x}#64 else 0x{loop:x}#64) x (run 1 s) := by
  rw [run_one, {prog}.stepi_eq_0x{cbz:x} hg.inv.program hg.pc hg.inv.err, hg.x13]
  exact gp_pc _ hg

theorem {P}_back{nr} {{s0 s : ArmState}} {{c : Call}} {{m : Nat}} {{x : BitVec 64}}
    (hg : GroupPost {layout} s0 c m 0x{sub:x}#64 x s) :
    GroupPost {layout} s0 c m (if x - 1#64 = 0#64 then 0x{tail:x}#64 else 0x{loop:x}#64) (x - 1#64)
      (run 2 s) := by
  rw [run_two, {prog}.stepi_eq_0x{sub:x} hg.inv.program hg.pc hg.inv.err, hg.x13]
  have hi : LoopInv {layout} s0 c m (w (.GPR 13#5) (x - 1#64) (w .PC 0x{sub+4:x}#64 s)) :=
    (hg.inv.w_other _ _ (Or.inl rfl)).w_other _ _ (Or.inr (Or.inl rfl))
  have hpc : r .PC (w (.GPR 13#5) (x - 1#64) (w .PC 0x{sub+4:x}#64 s)) = 0x{sub+4:x}#64 := by
    rw [r_of_w_different (by decide), r_of_w_same]
  rw [{prog}.stepi_eq_0x{sub+4:x} hi.program hpc hi.err, r_of_w_same]
  refine ⟨hi.w_other _ _ (Or.inl rfl), ?_, ?_⟩
  · rw [r_of_w_same]
    by_cases h0 : x - 1#64 = 0#64 <;> simp [h0]
  · rw [r_of_w_different (by decide), r_of_w_same]""")
    for (b, A_and, A_chunk, skip) in sec["tests"]:
        a(f"""
theorem {P}_test{nr}_{b} {{s0 s : ArmState}} {{c : Call}} {{m : Nat}} {{x : BitVec 64}}
    (hg : GroupPost {layout} s0 c m 0x{A_and:x}#64 x s) :
    GroupPost {layout} s0 c m (if arg s0 5 &&& {b}#64 = 0#64 then 0x{skip:x}#64 else 0x{A_chunk:x}#64) x
      (run 2 s) := by
  rw [run_two, {prog}.stepi_eq_0x{A_and:x} hg.inv.program hg.pc hg.inv.err, hg.inv.rem]
  have hi : LoopInv {layout} s0 c m (w (.GPR 16#5) (arg s0 5 &&& {b}#64) (w .PC 0x{A_and+4:x}#64 s)) :=
    (hg.inv.w_other _ _ (Or.inl rfl)).w_other _ _ (Or.inr (Or.inr rfl))
  have hpc : r .PC (w (.GPR 16#5) (arg s0 5 &&& {b}#64) (w .PC 0x{A_and+4:x}#64 s)) = 0x{A_and+4:x}#64 := by
    rw [r_of_w_different (by decide), r_of_w_same]
  rw [{prog}.stepi_eq_0x{A_and+4:x} hi.program hpc hi.err, r_of_w_same]
  refine ⟨hi.w_other _ _ (Or.inl rfl), r_of_w_same, ?_⟩
  rw [r_of_w_different (by decide), r_of_w_different (by decide), r_of_w_different (by decide)]
  exact hg.x13""")
    a(f"""
theorem {P}_ret{nr} {{s0 s : ArmState}} {{c : Call}} {{x : BitVec 64}}
    (hg : GroupPost {layout} s0 c c.nblocks 0x{ret:x}#64 x s) : Post c s0 (run 1 s) := by
  rw [run_one, {prog}.stepi_eq_0x{ret:x} hg.inv.program hg.pc hg.inv.err]
  have hi := hg.inv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [r_of_w_different (by decide)]; exact hi.err
  · rw [r_of_w_same]; exact hi.x30
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [r_of_w_different (by decide)]
    · exact hi.x18
    · exact hi.x28
    · exact hi.x29
    · exact hi.x30
    · exact hi.sp
  · intro j hj; simp only [block, read_mem_bytes_of_w]; exact hi.done j hj
  · intro a k hk; rw [read_mem_bytes_of_w]; exact hi.frame a k hk""")
    return "\n".join(L)


def main():
    prog_path, ns, prog, layout, P, outdir = sys.argv[1:7]
    insts = parse_program(prog_path)
    A = analyse(insts)
    lens = {}
    groups = []
    for nr, sec in A["secs"].items():
        groups.append(f"{P}_loop{nr}:{nr}:0x{sec['loop']:x}:0x{sec['sub']:x}:{G}")
        for (b, A_and, A_chunk, skip) in sec["tests"]:
            groups.append(f"{P}_chunk{nr}_{b}:{nr}:0x{A_chunk:x}:0x{skip:x}:{b}")
        lens[nr] = dict(loop=(sec["sub"] - sec["loop"]) // 4,
                        chunk={b: (skip - A_chunk) // 4 for (b, _, A_chunk, skip) in sec["tests"]})
    Pc = P[0].upper() + P[1:]
    with open(f"{outdir}/{Pc}Groups.txt", "w") as f:
        f.write("\n".join(groups) + "\n")
    mod = prog_path.split("lean/")[-1].removesuffix(".lean").replace("/", ".")
    L = ["/- Generated by tools/gen_bulk_ctl.py; do not edit. -/",
         "import Tactics.Sym", "import Tactics.Aggregate", f"import {mod}Steps", f"import {mod}Layout",
         "import AesCtr.Compose",
         "", f"namespace {ns}", "open AesCtr", "",
         "set_option maxRecDepth 100000", "set_option maxHeartbeats 0",
         "set_option linter.unusedVariables false"]
    keyEnd = G + 15 - 1
    for nr in (10, 12, 14):
        text, T = prologue(A, prog, layout, P, nr, A["secs"][nr], keyEnd)
        L.append(text)
        lens[nr]["pro"] = T
        L.append(ctl_lemmas(prog, layout, P, nr, A["secs"][nr]))
    L.append(f"end {ns}")
    with open(f"{outdir}/{Pc}Ctl.lean", "w") as f:
        f.write("\n".join(L) + "\n")
    print(lens)


if __name__ == "__main__":
    main()
