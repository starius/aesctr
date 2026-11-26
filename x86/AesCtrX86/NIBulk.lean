/-
The AES-NI path of `ctrBlocksBulkAsm`, composed: the entry, the loop of 8
blocks while 8 or more are left, the groups of 4, 2 and 1 blocks of the tail,
and `ret`.
-/
import AesCtrX86.NIGroups
import AesCtrX86.NIEnds

namespace AesCtrX86

/-! ## The groups, for any key size -/

theorem ni_tail4 (c : Call) (v : Bool) (hc : Pre c v) (b r0 : Nat) (hr0 : r0 < 8) (hb : b + r0 % 8 = c.n)
    (Q : MachineState → Prop) (s : MachineData) (hs : NIRegs c b s)
    (hrdi : s.regs.rdi.toBitVec = BitVec.ofNat 64 r0)
    (kont : ∀ (b' : Nat) (s' : MachineData), b' = (if 4 ≤ r0 % 8 then b + 4 else b) →
      NIRegs c b' s' → s'.regs.rdi.toBitVec = BitVec.ofNat 64 r0 → Runs exe Q (s', 0x5431c6)) :
    Runs exe Q (s, 0x542f49) := by
  rcases hc.nr with hnr | hnr | hnr
  · exact ni_tail4_10 c v hc hnr b r0 hr0 hb Q s hs hrdi kont
  · exact ni_tail4_12 c v hc hnr b r0 hr0 hb Q s hs hrdi kont
  · exact ni_tail4_14 c v hc hnr b r0 hr0 hb Q s hs hrdi kont

theorem ni_tail2 (c : Call) (v : Bool) (hc : Pre c v) (b r0 : Nat) (hr0 : r0 < 8) (hb : b + r0 % 4 = c.n)
    (Q : MachineState → Prop) (s : MachineData) (hs : NIRegs c b s)
    (hrdi : s.regs.rdi.toBitVec = BitVec.ofNat 64 r0)
    (kont : ∀ (b' : Nat) (s' : MachineData), b' = (if 2 ≤ r0 % 4 then b + 2 else b) →
      NIRegs c b' s' → s'.regs.rdi.toBitVec = BitVec.ofNat 64 r0 → Runs exe Q (s', 0x543347)) :
    Runs exe Q (s, 0x5431c6) := by
  rcases hc.nr with hnr | hnr | hnr
  · exact ni_tail2_10 c v hc hnr b r0 hr0 hb Q s hs hrdi kont
  · exact ni_tail2_12 c v hc hnr b r0 hr0 hb Q s hs hrdi kont
  · exact ni_tail2_14 c v hc hnr b r0 hr0 hb Q s hs hrdi kont

theorem ni_tail1 (c : Call) (v : Bool) (hc : Pre c v) (b r0 : Nat) (hr0 : r0 < 8) (hb : b + r0 % 2 = c.n)
    (Q : MachineState → Prop) (s : MachineData) (hs : NIRegs c b s)
    (hrdi : s.regs.rdi.toBitVec = BitVec.ofNat 64 r0)
    (kont : ∀ (b' : Nat) (s' : MachineData), b' = (if 1 ≤ r0 % 2 then b + 1 else b) →
      NIFinal c b' s' → s'.regs.rdi.toBitVec = BitVec.ofNat 64 r0 → Runs exe Q (s', 0x54343b)) :
    Runs exe Q (s, 0x543347) := by
  rcases hc.nr with hnr | hnr | hnr
  · exact ni_tail1_10 c v hc hnr b r0 hr0 hb Q s hs hrdi kont
  · exact ni_tail1_12 c v hc hnr b r0 hr0 hb Q s hs hrdi kont
  · exact ni_tail1_14 c v hc hnr b r0 hr0 hb Q s hs hrdi kont

theorem ni_loop (c : Call) (v : Bool) (hc : Pre c v) (b : Nat) (hb : b + 8 ≤ c.n)
    (Q : MachineState → Prop) (s : MachineData) (hs : NIRegs c b s)
    (hrdi : s.regs.rdi.toBitVec = BitVec.ofNat 64 (c.n - b))
    (hx11 : BitVec.setWidth 128 s.zmms.zmm11 = BitVec.ofNat 128 8)
    (kloop : ∀ s' : MachineData, NIRegs c (b + 8) s' →
      s'.regs.rdi.toBitVec = BitVec.ofNat 64 (c.n - (b + 8)) →
      BitVec.setWidth 128 s'.zmms.zmm11 = BitVec.ofNat 128 8 → b + 16 ≤ c.n →
      Runs exe Q (s', 0x542ad9))
    (ktail : ∀ s' : MachineData, NIRegs c (b + 8) s' →
      s'.regs.rdi.toBitVec = BitVec.ofNat 64 (c.n - (b + 8)) → c.n < b + 16 →
      Runs exe Q (s', 0x542f49)) :
    Runs exe Q (s, 0x542ad9) := by
  rcases hc.nr with hnr | hnr | hnr
  · exact ni_loop_10 c v hc hnr b hb Q s hs hrdi hx11 kloop ktail
  · exact ni_loop_12 c v hc hnr b hb Q s hs hrdi hx11 kloop ktail
  · exact ni_loop_14 c v hc hnr b hb Q s hs hrdi hx11 kloop ktail

/-! ## The path -/

/-- The tail, with `r0 < 8` blocks left after block `b`, and `ret`. -/
theorem ni_tail (c : Call) (v : Bool) (hc : Pre c v) (hrsp : c.regs.rsp.toBitVec = c.rsp)
    (b r0 : Nat) (hr0 : r0 < 8) (hb : b + r0 = c.n) (s : MachineData) (hs : NIRegs c b s)
    (hrdi : s.regs.rdi.toBitVec = BitVec.ofNat 64 r0) :
    Runs exe (Post c) (s, 0x542f49) := by
  refine ni_tail4 c v hc b r0 hr0 (by omega) _ s hs hrdi fun b1 s1 hb1 hs1 hrdi1 => ?_
  refine ni_tail2 c v hc b1 r0 hr0 (by split at hb1 <;> omega) _ s1 hs1 hrdi1
    fun b2 s2 hb2 hs2 hrdi2 => ?_
  refine ni_tail1 c v hc b2 r0 hr0 (by split at hb2 <;> split at hb1 <;> omega) _ s2 hs2
    hrdi2 fun b3 s3 hb3 hs3 _ => ?_
  have h3 : b3 = c.n := by split at hb3 <;> split at hb2 <;> split at hb1 <;> omega
  subst h3
  exact ni_ret c v hc hrsp s3 hs3

/-- The loop from block `b`, with 8 or more blocks left, then the tail. -/
theorem ni_loop_tail (c : Call) (v : Bool) (hc : Pre c v) (hrsp : c.regs.rsp.toBitVec = c.rsp)
    (b : Nat) (hb : b + 8 ≤ c.n) (s : MachineData) (hs : NIRegs c b s)
    (hrdi : s.regs.rdi.toBitVec = BitVec.ofNat 64 (c.n - b))
    (hx11 : BitVec.setWidth 128 s.zmms.zmm11 = BitVec.ofNat 128 8) :
    Runs exe (Post c) (s, 0x542ad9) :=
  ni_loop c v hc b hb _ s hs hrdi hx11
    (fun s' hs' hrdi' hx11' hmore =>
      ni_loop_tail c v hc hrsp (b + 8) (by omega) s' hs' hrdi' hx11')
    (fun s' hs' hrdi' _ =>
      ni_tail c v hc hrsp (b + 8) (c.n - (b + 8)) (by omega) (by omega) s' hs' hrdi')
termination_by c.n - b
decreasing_by omega

/-- The AES-NI path: called with `vaes = false`, `ctrBlocksBulkAsm` returns,
and then `dst` holds `src` XOR the keystream (`Post`). -/
theorem ni_correct (c : Call) (hc : Pre c false) (hrsp : c.regs.rsp.toBitVec = c.rsp)
    (zmms : RegZmms) (flags : StatusFlags) :
    Reaches exe (Post c) (⟨c.regs, zmms, flags, c.mem⟩, 0x542a80) :=
  reaches_of_runs <| ni_entry c hc hrsp (Post c) zmms flags
    (fun s hs hrdi hsmall => ni_tail c false hc hrsp 0 c.n hsmall (by omega) s hs hrdi)
    (fun s hs hrdi hx11 hb => ni_loop_tail c false hc hrsp 0 hb s hs hrdi hx11)

end AesCtrX86
