#!/usr/bin/env python3
"""Write AesCtrX86/NIGroups.lean: one lemma per group of the AES-NI path of
ctrBlocksBulkAsm and key size.

Usage: gen_groups.py <NIGroups.lean> [<VGroups.lean>]

Each lemma runs one group of blocks from its label to the label after it:
the counters, round 0, the branch on the key size, the rounds, the last round
with the source folded into the round key, the stores and (except for the last
group) the step of the pointers and the counter. It takes the state between
groups (NIRegs) and gives it back for the blocks after the group.
"""
import sys

OFF = 0x55c940          # ctrOffsets in the linked binary

# name, entry label, R192 label, R128 label, exit label, registers (blocks).
GROUPS = [
    ("tail4", 0x542f29, 0x542fe2, 0x543022, 0x5431a6, 4),
    ("tail2", 0x5431a6, 0x543213, 0x54323b, 0x543327, 2),
    ("tail1", 0x543327, 0x543370, 0x54338c, 0x54341b, 1),
]
LOOP = ("loop", 0x542ab9, 0x542bf5, 0x542c65, 0x542f29, 8)


def stores_term(j):
    """The memory after storing blocks b .. b+j-1 of dst, as Kraken writes it."""
    t = "s.dmem"
    for i in range(j):
        t = "(Mem.storeInt %s (blockAddr c.dst %s) 16 v%d)" % (t, bidx(i), i)
    return t


def bidx(i):
    return "b" if i == 0 else "(b + %d)" % i


def vs(j):
    return " ".join("v%d" % i for i in range(j))


def store_list(j):
    return "[" + ", ".join("(%s, v%d)" % (bidx(i), i) for i in range(j)) + "]"


def facts(k, nr, step):
    """`have`s for the loads of a group of k blocks with nr rounds; `step` is
    the ctrOffsets entry the group adds to the counter at its end (or None)."""
    out = []
    names = []
    out.append("have hinv := hs.mem")
    for r in range(nr + 1):
        addr = "c.xk" if r == 0 else "(c.xk + BitVec.ofNat 64 %d)" % (16 * r)
        out.append("have k%d : Mem.loadInt s.dmem %s 16 = some ((c.rk %d).toNat : Int) := by\n"
                   "      simpa [blockAddr] using key_fact hc.toBufs hinv (by omega) %d (by omega)" % (r, addr, r, r))
        names.append("k%d" % r)
    for j in range(1, k):
        out.append("have o%d : Mem.loadInt s.dmem %d#64 16 = some %d := by\n"
                   "      simpa [stores, offAddr] using off_fact hc hinv (by omega) %d (by omega) [] (by simp)"
                   % (j, OFF + 16 * j, j, j))
        names.append("o%d" % j)
    for j in range(k):
        q = "∀ %s : Int, " % vs(j) if j else ""
        lam = "fun %s => " % vs(j) if j else ""
        out.append("have s%d : %sMem.loadInt %s (blockAddr c.src %s) 16 =\n"
                   "        some ((c.srcb %s).toNat : Int) :=\n"
                   "      %ssrc_fact hc.toBufs hinv %s (by omega) (by omega) %s (by simp; try omega)"
                   % (j, q, stores_term(j), bidx(j), bidx(j), lam, bidx(j), store_list(j)))
        out.append("obtain ⟨z%d, hz%d⟩ := hc.dsts %s (by omega)" % (j, j, bidx(j)))
        out.append("have d%d : %sMem.loadInt %s (blockAddr c.dst %s) 16 = some z%d :=\n"
                   "      %s(dst_fact hc.toBufs hinv %s (by omega) (by omega) %s (by simp; try omega)).trans hz%d"
                   % (j, q, stores_term(j), bidx(j), j, lam, bidx(j), store_list(j), j))
        names += ["s%d" % j, "d%d" % j]
    if step is not None:
        q = "∀ %s : Int, " % vs(k)
        out.append("have ostep : %sMem.loadInt %s %d#64 16 = some %d := fun %s => by\n"
                   "      simpa [stores, offAddr] using off_fact hc hinv (by omega) %d (by omega) %s (by simp; omega)"
                   % (q, stores_term(k), OFF + 16 * step, step, vs(k), step, store_list(k)))
        names.append("ostep")
    return out, names


def mem_proof(k, indent, tag="", out="out_eq"):
    """MemInv c (b + k) for the stores of the group, outermost store first.
    The holes are named after tag, which differs between the branches of a
    lemma. out is the lemma for the value stored (out_eq' where the source
    block is XORed into the last round key, rather than the key into it)."""
    lines = []
    for j in reversed(range(k)):
        lines.append("refine memInv_store' hc.toBufs (b := %s) (by omega) ?m%s%d (by omega) _ ?v%s%d"
                     % (bidx(j), tag, j, tag, j))
        lines.append("case v%s%d =>" % (tag, j))
        lines.append("  rw [← %s c %s (by have := hc.ctr; omega)]" % (out, bidx(j)))
        lines.append("  simp only [hnr, encRounds, Nat.reduceAdd, Nat.reduceSub]")
    lines.append("exact hs.mem")
    return [indent + l for l in lines]


def lemma(group, nr, kind):
    name, entry, r192, r128, exit_, k = group
    step = k if kind == "tail" else None
    fs, fnames = facts(k, nr, step)
    blocks = "next_%x, blk_%x, next_%x, blk_%x" % (r192, r192, r128, r128)
    regs = "hrax, hrbx, hrsi, hrdx, hx9, hx10"
    L = []
    if kind in ("tail", "last"):
        L.append("""/-- The AES-NI group of %(k)d blocks at %(entry)x, AES-%(bits)d: if bit %(k)d of the
remaining count is set, it encrypts blocks `b .. b+%(km1)d`%(stepdoc)s. -/
theorem ni_%(name)s_%(nr)d (c : Call) (v : Bool) (hc : Pre c v) (hnr : c.nr = %(nr)d)
    (b r0 : Nat) (hr0 : r0 < 8) (hb : b + r0 %% %(k2)d = c.n)
    (Q : MachineState → Prop) (s : MachineData) (hs : NIRegs c b s)
    (hrdi : s.regs.rdi.toBitVec = BitVec.ofNat 64 r0)
    (kont : ∀ (b' : Nat) (s' : MachineData), b' = (if %(k)d ≤ r0 %% %(k2)d then b + %(k)d else b) →
      %(post)s c b' s' → s'.regs.rdi.toBitVec = BitVec.ofNat 64 r0 → Runs exe Q (s', 0x%(exit)x)) :
    Runs exe Q (s, 0x%(entry)x) := by
  have hrax : s.regs.rax.toBitVec = BitVec.ofNat 64 %(nr)d := by rw [hs.rax, hnr]
  have hrbx := hs.rbx
  have hrsi := hs.rsi
  have hrdx := hs.rdx
  have hx9 := hs.x9
  have hx10 := hs.x10
  have hbit := test_bit_%(k)d r0 hr0
  rw [runs_def, next_%(entry)x]
  simp only [blk_%(entry)x]
  by_cases hrun : %(k)d ≤ r0 %% %(k2)d
  case neg =>
    xstep [%(regs)s, hrdi, hbit, hrun, label_%(exit)x]
    intros
    apply reaches_of_runs
    exact kont b _ (by simp [hrun]) %(skipstate)s hrdi
  case pos =>
""" % dict(name=name, nr=nr, k=k, k2=2 * k, km1=k - 1, entry=entry, exit=exit_,
           bits={10: 128, 12: 192, 14: 256}[nr], regs=regs,
           stepdoc="" if kind == "last" else ", and steps the pointers and the counter",
           skipstate="(niRegs_status hs _).final" if kind == "last" else "(niRegs_status hs _)",
           post="NIFinal" if kind == "last" else "NIRegs"))
        indent = "    "
        L.append(indent + "have hbk : b + %d ≤ c.n := by omega" % k)
        for f in fs:
            L.append(indent + f)
        first = "xstep [%s, hrdi, hbit, hrun, %s, %s, label_%x, label_%x]" % (
            regs, ", ".join(fnames), blocks, r128, r192)
    else:
        L.append("""/-- One iteration of the AES-NI loop at %(entry)x, AES-%(bits)d: it encrypts
blocks `b .. b+7`, steps the pointers and the counter, and goes back to the
loop while 8 or more blocks are left. -/
theorem ni_loop_%(nr)d (c : Call) (v : Bool) (hc : Pre c v) (hnr : c.nr = %(nr)d)
    (b : Nat) (hb : b + 8 ≤ c.n)
    (Q : MachineState → Prop) (s : MachineData) (hs : NIRegs c b s)
    (hrdi : s.regs.rdi.toBitVec = BitVec.ofNat 64 (c.n - b))
    (hx11 : BitVec.setWidth 128 s.zmms.zmm11 = BitVec.ofNat 128 8)
    (kloop : ∀ s' : MachineData, NIRegs c (b + 8) s' →
      s'.regs.rdi.toBitVec = BitVec.ofNat 64 (c.n - (b + 8)) →
      BitVec.setWidth 128 s'.zmms.zmm11 = BitVec.ofNat 128 8 → b + 16 ≤ c.n →
      Runs exe Q (s', 0x%(entry)x))
    (ktail : ∀ s' : MachineData, NIRegs c (b + 8) s' →
      s'.regs.rdi.toBitVec = BitVec.ofNat 64 (c.n - (b + 8)) → c.n < b + 16 →
      Runs exe Q (s', 0x%(exit)x)) :
    Runs exe Q (s, 0x%(entry)x) := by
  have hrax : s.regs.rax.toBitVec = BitVec.ofNat 64 %(nr)d := by rw [hs.rax, hnr]
  have hrbx := hs.rbx
  have hrsi := hs.rsi
  have hrdx := hs.rdx
  have hx9 := hs.x9
  have hx10 := hs.x10
  have hn64 : c.n - b < 2 ^ 64 := by have := hc.src_fit; omega
  have hsub : BitVec.ofNat 64 (c.n - b) - BitVec.ofNat 64 8 = BitVec.ofNat 64 (c.n - (b + 8)) :=
    (ofNat_sub_ofNat _ _ (by omega) hn64).trans (by rw [Nat.sub_sub])
  have hn64' : c.n - (b + 8) < 2 ^ 64 := by omega
  rw [runs_def, next_%(entry)x]
  simp only [blk_%(entry)x]
""" % dict(nr=nr, entry=entry, exit=exit_, bits={10: 128, 12: 192, 14: 256}[nr]))
        indent = "  "
        for f in fs:
            L.append(indent + f)
        first = "xstep [%s, hrdi, hx11, hsub, hn64', %s, %s, label_%x, label_%x, label_%x]" % (
            regs, ", ".join(fnames), blocks, r128, r192, entry)
    # Run the blocks: jumps to R128 (AES-128) or R192 (AES-192) end a
    # straight-line run; AES-256 falls through.
    L.append(indent + first)
    L.append(indent + "intros")
    if nr in (10, 12):
        tgt = r128 if nr == 10 else r192
        L.append(indent + "apply reaches_of_runs")
        L.append(indent + "rw [runs_def]")
        L.append(indent + "xstep [%s, %s, %s]" % (regs, ", ".join(fnames),
                                                  blocks if kind != "loop" else blocks + ", hrdi, hx11, hsub, hn64', label_%x" % entry))
        L.append(indent + "intros")
    # The end of the group.
    if kind == "loop":
        regs_post = ["refine ⟨hs.rax, hs.rbx, rfl, rfl, hs.rsp, hs.rbp, hs.r14, hs.r15,",
                     "  by simp only [setWidth_replaceLow_zmm], hs.x10, ?_⟩"]
        L.append(indent + "by_cases hmore : b + 16 ≤ c.n")
        L.append(indent + "· -- 8 or more blocks left: back to the loop")
        L.append(indent + "  have hcond : (c.n - (b + 8) < 8) = False := by simp only [eq_iff_iff, iff_false]; omega")
        L.append(indent + "  simp only [hcond, decide_false, Bool.not_false, ite_true, Effects.All]")
        L.append(indent + "  apply reaches_of_runs")
        L.append(indent + "  apply kloop")
        L.append(indent + "  · " + regs_post[0])
        L.append(indent + "      " + regs_post[1])
        L += mem_proof(8, indent + "    ", "a")
        L.append(indent + "  · rfl")
        L.append(indent + "  · exact hx11")
        L.append(indent + "  · exact hmore")
        L.append(indent + "· -- fewer than 8 blocks left: the tail")
        L.append(indent + "  have hcond : (c.n - (b + 8) < 8) = True := by simp only [eq_iff_iff, iff_true]; omega")
        L.append(indent + "  simp only [hcond, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]")
        L.append(indent + "  rw [← runs_def]")
        L.append(indent + "  apply ktail")
        L.append(indent + "  · " + regs_post[0])
        L.append(indent + "      " + regs_post[1])
        L += mem_proof(8, indent + "    ", "b")
        L.append(indent + "  · rfl")
        L.append(indent + "  · omega")
    else:
        L.append(indent + "rw [← runs_def]")
        L.append(indent + "apply kont (b + %d) _ (by simp [hrun])" % k)
        if kind == "last":
            L.append(indent + "· refine ⟨hs.rsp, hs.rbp, hs.r14, hs.r15, ?_⟩")
        else:
            L.append(indent + "· refine ⟨hs.rax, hs.rbx, rfl, rfl, hs.rsp, hs.rbp, hs.r14, hs.r15,")
            L.append(indent + "    by simp only [setWidth_replaceLow_zmm], hs.x10, ?_⟩")
        L += mem_proof(k, indent + "  ")
        L.append(indent + "· exact hrdi")
    return "\n".join(L) + "\n"


# The VAES path: name, entry label, R192 label, R128 label, exit label, blocks.
# The groups of 16, 8, 4 and 2 blocks use ymm registers (two blocks each), the
# group of 1 block an xmm register.
VGROUPS = [
    ("tail8", 0x543809, 0x5438a6, 0x5438de, 0x543a2d, 8),
    ("tail4", 0x543a2d, 0x543a92, 0x543ab6, 0x543b87, 4),
    ("tail2", 0x543b87, 0x543bd0, 0x543bea, 0x543c7f, 2),
    ("tail1", 0x543c7f, 0x543cc5, 0x543cdd, 0x543d52, 1),
]
VLOOP = ("loop", 0x543449, 0x54354d, 0x5435ad, 0x543809, 16)


def vfacts(k, nr, step):
    """`have`s for the loads of a VAES group of k blocks with nr rounds."""
    out = ["have hinv := hs.mem"]
    names = []
    for r in range(nr + 1):
        addr = "c.xk" if r == 0 else "(c.xk + BitVec.ofNat 64 %d)" % (16 * r)
        out.append("have k%d : Mem.loadInt s.dmem %s 16 = some ((c.rk %d).toNat : Int) := by\n"
                   "      simpa [blockAddr] using key_fact hc.toBufs hinv (by omega) %d (by omega)" % (r, addr, r, r))
        names.append("k%d" % r)
    if k == 1:
        out.append("have o0 : Mem.loadInt s.dmem %d#64 16 = some 0 := by\n"
                   "      simpa [stores, offAddr] using off_fact hc hinv (by omega) 0 (by omega) [] (by simp)"
                   % OFF)
        names.append("o0")
        out.append("have s0 : Mem.loadInt s.dmem (blockAddr c.src b) 16 =\n"
                   "        some ((c.srcb b).toNat : Int) :=\n"
                   "      src_fact hc.toBufs hinv b (by omega) (by omega) [] (by simp)")
        out.append("obtain ⟨z0, hz0⟩ := hc.dsts b (by omega)")
        out.append("have d0 : Mem.loadInt s.dmem (blockAddr c.dst b) 16 = some z0 :=\n"
                   "      (dst_fact hc.toBufs hinv b (by omega) (by omega) [] (by simp)).trans hz0")
        names += ["s0", "d0"]
        return out, names
    for j in range(k // 2):
        a = OFF + 32 * j
        out.append("have o%d : Mem.loadInt s.dmem %d#64 32 = some %d := by\n"
                   "      have h0 : Mem.loadInt s.dmem %d#64 16 = some %d := by\n"
                   "        simpa [stores, offAddr] using off_fact hc hinv (by omega) %d (by omega) [] (by simp)\n"
                   "      have h1 : Mem.loadInt s.dmem (%d#64 + 16#64) 16 = some %d := by\n"
                   "        simpa [stores, offAddr] using off_fact hc hinv (by omega) %d (by omega) [] (by simp)\n"
                   "      rw [loadInt_32 _ _ _ _ h0 h1]\n"
                   "      simp"
                   % (j, a, 2 * j + 2 ** 128 * (2 * j + 1), a, 2 * j, 2 * j, a, 2 * j + 1, 2 * j + 1))
        names.append("o%d" % j)
    for j in range(k // 2):
        i0, i1 = 2 * j, 2 * j + 1
        q = "∀ %s : Int, " % vs(i0) if i0 else ""
        lam = "fun %s => " % vs(i0) if i0 else ""
        app = " " + vs(i0) if i0 else ""
        mem = stores_term(i0)
        for i in (i0, i1):
            out.append("have s%d : %sMem.loadInt %s (blockAddr c.src %s) 16 =\n"
                       "        some ((c.srcb %s).toNat : Int) :=\n"
                       "      %ssrc_fact hc.toBufs hinv %s (by omega) (by omega) %s (by simp; try omega)"
                       % (i, q, mem, bidx(i), bidx(i), lam, bidx(i), store_list(i0)))
            out.append("obtain ⟨z%d, hz%d⟩ := hc.dsts %s (by omega)" % (i, i, bidx(i)))
            out.append("have d%d : %sMem.loadInt %s (blockAddr c.dst %s) 16 = some z%d :=\n"
                       "      %s(dst_fact hc.toBufs hinv %s (by omega) (by omega) %s (by simp; try omega)).trans hz%d"
                       % (i, q, mem, bidx(i), i, lam, bidx(i), store_list(i0), i))
        out.append("have S%d : %sMem.loadInt %s (blockAddr c.src %s) 32 =\n"
                   "        some ((c.srcb %s ++ c.srcb %s).toNat : Int) :=\n"
                   "      %sloadInt_32_blk _ _ _ _ _ (s%d%s) (s%d%s)"
                   % (j, q, mem, bidx(i0), bidx(i1), bidx(i0), lam, i0, app, i1, app))
        out.append("have D%d : %sMem.loadInt %s (blockAddr c.dst %s) 32 = some (z%d + 2 ^ 128 * z%d) :=\n"
                   "      %sloadInt_32_blk' _ _ _ _ _ (d%d%s) (d%d%s)"
                   % (j, q, mem, bidx(i0), i0, i1, lam, i0, app, i1, app))
        names += ["S%d" % j, "D%d" % j]
    if step is not None:
        q = "∀ %s : Int, " % vs(k)
        out.append("have ostep : %sMem.loadInt %s %d#64 16 = some %d := fun %s => by\n"
                   "      simpa [stores, offAddr] using off_fact hc hinv (by omega) %d (by omega) %s (by simp; omega)"
                   % (q, stores_term(k), OFF + 16 * step, step, vs(k), step, store_list(k)))
        names.append("ostep")
    return out, names


def vlemma(group, nr, kind):
    name, entry, r192, r128, exit_, k = group
    step = k if kind == "tail" else None
    fs, fnames = vfacts(k, nr, step)
    blocks = "next_%x, blk_%x, next_%x, blk_%x" % (r192, r192, r128, r128)
    if k == 1:
        regs = "hrax, hrbx, hrsi, hrdx, hx9, hx10"
        regdefs = "  have hx9 := hs.x9\n  have hx10 := hs.x10\n"
    else:
        regs = "hrax, hrbx, hrsi, hrdx, hy9, hy10"
        regdefs = "  have hy9 := hs.y9\n  have hy10 := hs.y10\n"
    L = []
    if kind in ("tail", "last"):
        L.append("""/-- The VAES group of %(k)d blocks at %(entry)x, AES-%(bits)d: if bit %(k)d of the
remaining count is set, it encrypts blocks `b .. b+%(km1)d`%(stepdoc)s. -/
theorem v_%(name)s_%(nr)d (c : Call) (v : Bool) (hc : Pre c v) (hnr : c.nr = %(nr)d)
    (b r0 : Nat) (hr0 : r0 < 16) (hb : b + r0 %% %(k2)d = c.n)
    (Q : MachineState → Prop) (s : MachineData) (hs : VRegs c b s)
    (hrdi : s.regs.rdi.toBitVec = BitVec.ofNat 64 r0)
    (kont : ∀ (b' : Nat) (s' : MachineData), b' = (if %(k)d ≤ r0 %% %(k2)d then b + %(k)d else b) →
      %(post)s c b' s' → s'.regs.rdi.toBitVec = BitVec.ofNat 64 r0 → Runs exe Q (s', 0x%(exit)x)) :
    Runs exe Q (s, 0x%(entry)x) := by
  have hrax : s.regs.rax.toBitVec = BitVec.ofNat 64 %(nr)d := by rw [hs.rax, hnr]
  have hrbx := hs.rbx
  have hrsi := hs.rsi
  have hrdx := hs.rdx
%(regdefs)s  have hbit := vtest_bit_%(k)d r0 hr0
  rw [runs_def, next_%(entry)x]
  simp only [blk_%(entry)x]
  by_cases hrun : %(k)d ≤ r0 %% %(k2)d
  case neg =>
    vstep [%(regs)s, hrdi, hbit, hrun, label_%(exit)x]
    intros
    apply reaches_of_runs
    exact kont b _ (by simp [hrun]) %(skipstate)s hrdi
  case pos =>
""" % dict(name=name, nr=nr, k=k, k2=2 * k, km1=k - 1, entry=entry, exit=exit_,
           bits={10: 128, 12: 192, 14: 256}[nr], regs=regs, regdefs=regdefs,
           stepdoc="" if kind == "last" else ", and steps the pointers and the counter",
           skipstate="(vRegs_status hs _).final" if kind == "last" else "(vRegs_status hs _)",
           post="NIFinal" if kind == "last" else "VRegs"))
        indent = "    "
        L.append(indent + "have hbk : b + %d ≤ c.n := by omega" % k)
        for f in fs:
            L.append(indent + f)
        first = "vstep [%s, hrdi, hbit, hrun, %s, %s, label_%x, label_%x]" % (
            regs, ", ".join(fnames), blocks, r128, r192)
    else:
        L.append("""/-- One iteration of the VAES loop at %(entry)x, AES-%(bits)d: it encrypts
blocks `b .. b+15`, steps the pointers and the counter, and goes back to the
loop while 16 or more blocks are left. -/
theorem v_loop_%(nr)d (c : Call) (v : Bool) (hc : Pre c v) (hnr : c.nr = %(nr)d)
    (b : Nat) (hb : b + 16 ≤ c.n)
    (Q : MachineState → Prop) (s : MachineData) (hs : VRegs c b s)
    (hrdi : s.regs.rdi.toBitVec = BitVec.ofNat 64 (c.n - b))
    (hy11 : BitVec.setWidth 256 s.zmms.zmm11 = 16#128 ++ 16#128)
    (kloop : ∀ s' : MachineData, VRegs c (b + 16) s' →
      s'.regs.rdi.toBitVec = BitVec.ofNat 64 (c.n - (b + 16)) →
      BitVec.setWidth 256 s'.zmms.zmm11 = 16#128 ++ 16#128 → b + 32 ≤ c.n →
      Runs exe Q (s', 0x%(entry)x))
    (ktail : ∀ s' : MachineData, VRegs c (b + 16) s' →
      s'.regs.rdi.toBitVec = BitVec.ofNat 64 (c.n - (b + 16)) → c.n < b + 32 →
      Runs exe Q (s', 0x%(exit)x)) :
    Runs exe Q (s, 0x%(entry)x) := by
  have hrax : s.regs.rax.toBitVec = BitVec.ofNat 64 %(nr)d := by rw [hs.rax, hnr]
  have hrbx := hs.rbx
  have hrsi := hs.rsi
  have hrdx := hs.rdx
%(regdefs)s  have hn64 : c.n - b < 2 ^ 64 := by have := hc.src_fit; omega
  have hsub : BitVec.ofNat 64 (c.n - b) - BitVec.ofNat 64 16 = BitVec.ofNat 64 (c.n - (b + 16)) :=
    (ofNat_sub_ofNat _ _ (by omega) hn64).trans (by rw [Nat.sub_sub])
  have hn64' : c.n - (b + 16) < 2 ^ 64 := by omega
  rw [runs_def, next_%(entry)x]
  simp only [blk_%(entry)x]
""" % dict(nr=nr, entry=entry, exit=exit_, bits={10: 128, 12: 192, 14: 256}[nr], regdefs=regdefs))
        indent = "  "
        for f in fs:
            L.append(indent + f)
        first = "vstep [%s, hrdi, hy11, hsub, hn64', %s, %s, label_%x, label_%x, label_%x]" % (
            regs, ", ".join(fnames), blocks, r128, r192, entry)
    L.append(indent + first)
    L.append(indent + "intros")
    if nr in (10, 12):
        L.append(indent + "apply reaches_of_runs")
        L.append(indent + "rw [runs_def]")
        L.append(indent + "vstep [%s, %s, %s]" % (regs, ", ".join(fnames),
                                                  blocks if kind != "loop" else blocks + ", hrdi, hy11, hsub, hn64', label_%x" % entry))
        L.append(indent + "intros")
    if kind == "loop":
        regs_post = ["refine ⟨hs.rax, hs.rbx, rfl, rfl, hs.rsp, hs.rbp, hs.r14, hs.r15,",
                     "  by simp only [setWidth_256_512], hs.y10, ?_⟩"]
        L.append(indent + "by_cases hmore : b + 32 ≤ c.n")
        L.append(indent + "· -- 16 or more blocks left: back to the loop")
        L.append(indent + "  have hcond : (c.n - (b + 16) < 16) = False := by simp only [eq_iff_iff, iff_false]; omega")
        L.append(indent + "  simp only [hcond, decide_false, Bool.not_false, ite_true, Effects.All]")
        L.append(indent + "  apply reaches_of_runs")
        L.append(indent + "  apply kloop")
        L.append(indent + "  · " + regs_post[0])
        L.append(indent + "      " + regs_post[1])
        L += mem_proof(16, indent + "    ", "a", "out_eq'")
        L.append(indent + "  · rfl")
        L.append(indent + "  · exact hy11")
        L.append(indent + "  · exact hmore")
        L.append(indent + "· -- fewer than 16 blocks left: the tail")
        L.append(indent + "  have hcond : (c.n - (b + 16) < 16) = True := by simp only [eq_iff_iff, iff_true]; omega")
        L.append(indent + "  simp only [hcond, decide_true, Bool.not_true, Bool.false_eq_true, ite_false]")
        L.append(indent + "  rw [← runs_def]")
        L.append(indent + "  apply ktail")
        L.append(indent + "  · " + regs_post[0])
        L.append(indent + "      " + regs_post[1])
        L += mem_proof(16, indent + "    ", "b", "out_eq'")
        L.append(indent + "  · rfl")
        L.append(indent + "  · omega")
    else:
        L.append(indent + "rw [← runs_def]")
        L.append(indent + "apply kont (b + %d) _ (by simp [hrun])" % k)
        if kind == "last":
            L.append(indent + "· refine ⟨hs.rsp, hs.rbp, hs.r14, hs.r15, ?_⟩")
        else:
            L.append(indent + "· refine ⟨hs.rax, hs.rbx, rfl, rfl, hs.rsp, hs.rbp, hs.r14, hs.r15,")
            L.append(indent + "    by simp only [setWidth_256_512], hs.y10, ?_⟩")
        L += mem_proof(k, indent + "  ", "", "out_eq'")
        L.append(indent + "· exact hrdi")
    return "\n".join(L) + "\n"


VHEADER = """/-
Generated by gen_groups.py: do not edit.

The groups of the VAES path of ctrBlocksBulkAsm, one lemma per group and key
size.
-/
import AesCtrX86.VState

open Std Std.ExtHashMap

namespace AesCtrX86

set_option maxHeartbeats 40000000
set_option maxRecDepth 200000
"""


def main():
    dest = sys.argv[1]
    out = ["""/-
Generated by gen_groups.py: do not edit.

The groups of the AES-NI path of ctrBlocksBulkAsm, one lemma per group and key
size.
-/
import AesCtrX86.Tactic
import AesCtrX86.Reach
import AesCtrX86.NIState
import AesCtrX86.Values
import AesCtrX86.Flags

open Std Std.ExtHashMap

namespace AesCtrX86

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000
"""]
    for g in GROUPS:
        for nr in (10, 12, 14):
            out.append(lemma(g, nr, "last" if g[0] == "tail1" else "tail"))
    for nr in (10, 12, 14):
        out.append(lemma(LOOP, nr, "loop"))
    out.append("end AesCtrX86\n")
    open(dest, "w").write("\n".join(out))
    if len(sys.argv) > 2:
        out = [VHEADER]
        for g in VGROUPS:
            for nr in (10, 12, 14):
                out.append(vlemma(g, nr, "last" if g[0] == "tail1" else "tail"))
        for nr in (10, 12, 14):
            out.append(vlemma(VLOOP, nr, "loop"))
        out.append("end AesCtrX86\n")
        open(sys.argv[2], "w").write("\n".join(out))


main()
