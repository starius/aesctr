/-
The VAES path of `ctrBlocksBulkAsm`, composed: the entry, the loop of 16
blocks while 16 or more are left, the groups of 8, 4, 2 and 1 blocks of the
tail, and `vzeroupper; ret`. Then both paths: `ctrBlocksBulkAsm` is correct.
-/
import AesCtrX86.VGroups
import AesCtrX86.VEnds
import AesCtrX86.NIBulk

namespace AesCtrX86

/-! ## The groups, for any key size -/

theorem v_tail8 (c : Call) (v : Bool) (hc : Pre c v) (b r0 : Nat) (hr0 : r0 < 16)
    (hb : b + r0 % 16 = c.n) (Q : MachineState → Prop) (s : MachineData) (hs : VRegs c b s)
    (hrdi : s.regs.rdi.toBitVec = BitVec.ofNat 64 r0)
    (kont : ∀ (b' : Nat) (s' : MachineData), b' = (if 8 ≤ r0 % 16 then b + 8 else b) →
      VRegs c b' s' → s'.regs.rdi.toBitVec = BitVec.ofNat 64 r0 → Runs exe Q (s', 0x543a2d)) :
    Runs exe Q (s, 0x543809) := by
  rcases hc.nr with hnr | hnr | hnr
  · exact v_tail8_10 c v hc hnr b r0 hr0 hb Q s hs hrdi kont
  · exact v_tail8_12 c v hc hnr b r0 hr0 hb Q s hs hrdi kont
  · exact v_tail8_14 c v hc hnr b r0 hr0 hb Q s hs hrdi kont

theorem v_tail4 (c : Call) (v : Bool) (hc : Pre c v) (b r0 : Nat) (hr0 : r0 < 16)
    (hb : b + r0 % 8 = c.n) (Q : MachineState → Prop) (s : MachineData) (hs : VRegs c b s)
    (hrdi : s.regs.rdi.toBitVec = BitVec.ofNat 64 r0)
    (kont : ∀ (b' : Nat) (s' : MachineData), b' = (if 4 ≤ r0 % 8 then b + 4 else b) →
      VRegs c b' s' → s'.regs.rdi.toBitVec = BitVec.ofNat 64 r0 → Runs exe Q (s', 0x543b87)) :
    Runs exe Q (s, 0x543a2d) := by
  rcases hc.nr with hnr | hnr | hnr
  · exact v_tail4_10 c v hc hnr b r0 hr0 hb Q s hs hrdi kont
  · exact v_tail4_12 c v hc hnr b r0 hr0 hb Q s hs hrdi kont
  · exact v_tail4_14 c v hc hnr b r0 hr0 hb Q s hs hrdi kont

theorem v_tail2 (c : Call) (v : Bool) (hc : Pre c v) (b r0 : Nat) (hr0 : r0 < 16)
    (hb : b + r0 % 4 = c.n) (Q : MachineState → Prop) (s : MachineData) (hs : VRegs c b s)
    (hrdi : s.regs.rdi.toBitVec = BitVec.ofNat 64 r0)
    (kont : ∀ (b' : Nat) (s' : MachineData), b' = (if 2 ≤ r0 % 4 then b + 2 else b) →
      VRegs c b' s' → s'.regs.rdi.toBitVec = BitVec.ofNat 64 r0 → Runs exe Q (s', 0x543c7f)) :
    Runs exe Q (s, 0x543b87) := by
  rcases hc.nr with hnr | hnr | hnr
  · exact v_tail2_10 c v hc hnr b r0 hr0 hb Q s hs hrdi kont
  · exact v_tail2_12 c v hc hnr b r0 hr0 hb Q s hs hrdi kont
  · exact v_tail2_14 c v hc hnr b r0 hr0 hb Q s hs hrdi kont

theorem v_tail1 (c : Call) (v : Bool) (hc : Pre c v) (b r0 : Nat) (hr0 : r0 < 16)
    (hb : b + r0 % 2 = c.n) (Q : MachineState → Prop) (s : MachineData) (hs : VRegs c b s)
    (hrdi : s.regs.rdi.toBitVec = BitVec.ofNat 64 r0)
    (kont : ∀ (b' : Nat) (s' : MachineData), b' = (if 1 ≤ r0 % 2 then b + 1 else b) →
      NIFinal c b' s' → s'.regs.rdi.toBitVec = BitVec.ofNat 64 r0 → Runs exe Q (s', 0x543d52)) :
    Runs exe Q (s, 0x543c7f) := by
  rcases hc.nr with hnr | hnr | hnr
  · exact v_tail1_10 c v hc hnr b r0 hr0 hb Q s hs hrdi kont
  · exact v_tail1_12 c v hc hnr b r0 hr0 hb Q s hs hrdi kont
  · exact v_tail1_14 c v hc hnr b r0 hr0 hb Q s hs hrdi kont

theorem v_loop (c : Call) (v : Bool) (hc : Pre c v) (b : Nat) (hb : b + 16 ≤ c.n)
    (Q : MachineState → Prop) (s : MachineData) (hs : VRegs c b s)
    (hrdi : s.regs.rdi.toBitVec = BitVec.ofNat 64 (c.n - b))
    (hy11 : BitVec.setWidth 256 s.zmms.zmm11 = 16#128 ++ 16#128)
    (kloop : ∀ s' : MachineData, VRegs c (b + 16) s' →
      s'.regs.rdi.toBitVec = BitVec.ofNat 64 (c.n - (b + 16)) →
      BitVec.setWidth 256 s'.zmms.zmm11 = 16#128 ++ 16#128 → b + 32 ≤ c.n →
      Runs exe Q (s', 0x543449))
    (ktail : ∀ s' : MachineData, VRegs c (b + 16) s' →
      s'.regs.rdi.toBitVec = BitVec.ofNat 64 (c.n - (b + 16)) → c.n < b + 32 →
      Runs exe Q (s', 0x543809)) :
    Runs exe Q (s, 0x543449) := by
  rcases hc.nr with hnr | hnr | hnr
  · exact v_loop_10 c v hc hnr b hb Q s hs hrdi hy11 kloop ktail
  · exact v_loop_12 c v hc hnr b hb Q s hs hrdi hy11 kloop ktail
  · exact v_loop_14 c v hc hnr b hb Q s hs hrdi hy11 kloop ktail

/-! ## The path -/

/-- The tail, with `r0 < 16` blocks left after block `b`, and `vzeroupper; ret`. -/
theorem v_tail (c : Call) (v : Bool) (hc : Pre c v) (hrsp : c.regs.rsp.toBitVec = c.rsp)
    (b r0 : Nat) (hr0 : r0 < 16) (hb : b + r0 = c.n) (s : MachineData) (hs : VRegs c b s)
    (hrdi : s.regs.rdi.toBitVec = BitVec.ofNat 64 r0) :
    Runs exe (Post c) (s, 0x543809) := by
  refine v_tail8 c v hc b r0 hr0 (by omega) _ s hs hrdi fun b1 s1 hb1 hs1 hrdi1 => ?_
  refine v_tail4 c v hc b1 r0 hr0 (by split at hb1 <;> omega) _ s1 hs1 hrdi1
    fun b2 s2 hb2 hs2 hrdi2 => ?_
  refine v_tail2 c v hc b2 r0 hr0 (by split at hb2 <;> split at hb1 <;> omega) _ s2 hs2 hrdi2
    fun b3 s3 hb3 hs3 hrdi3 => ?_
  refine v_tail1 c v hc b3 r0 hr0 (by split at hb3 <;> split at hb2 <;> split at hb1 <;> omega)
    _ s3 hs3 hrdi3 fun b4 s4 hb4 hs4 _ => ?_
  have h4 : b4 = c.n := by
    split at hb4 <;> split at hb3 <;> split at hb2 <;> split at hb1 <;> omega
  subst h4
  exact v_ret c v hc hrsp s4 hs4

/-- The loop from block `b`, with 16 or more blocks left, then the tail. -/
theorem v_loop_tail (c : Call) (v : Bool) (hc : Pre c v) (hrsp : c.regs.rsp.toBitVec = c.rsp)
    (b : Nat) (hb : b + 16 ≤ c.n) (s : MachineData) (hs : VRegs c b s)
    (hrdi : s.regs.rdi.toBitVec = BitVec.ofNat 64 (c.n - b))
    (hy11 : BitVec.setWidth 256 s.zmms.zmm11 = 16#128 ++ 16#128) :
    Runs exe (Post c) (s, 0x543449) :=
  v_loop c v hc b hb _ s hs hrdi hy11
    (fun s' hs' hrdi' hy11' _ =>
      v_loop_tail c v hc hrsp (b + 16) (by omega) s' hs' hrdi' hy11')
    (fun s' hs' hrdi' _ =>
      v_tail c v hc hrsp (b + 16) (c.n - (b + 16)) (by omega) (by omega) s' hs' hrdi')
termination_by c.n - b
decreasing_by omega

/-- The VAES path: called with `vaes = true`, `ctrBlocksBulkAsm` returns, and
then `dst` holds `src` XOR the keystream (`Post`). -/
theorem v_correct (c : Call) (hc : Pre c true) (hrsp : c.regs.rsp.toBitVec = c.rsp)
    (zmms : RegZmms) (flags : StatusFlags) :
    Reaches exe (Post c) (⟨c.regs, zmms, flags, c.mem⟩, 0x542a60) :=
  reaches_of_runs <| v_entry c hc hrsp (Post c) zmms flags
    (fun s hs hrdi hsmall => v_tail c true hc hrsp 0 c.n hsmall (by omega) s hs hrdi)
    (fun s hs hrdi hy11 hb => v_loop_tail c true hc hrsp 0 hb s hs hrdi hy11)

/-- `ctrBlocksBulkAsm` is correct: called as the contract `Pre` says, with
either value of `vaes`, every run returns to the caller with `dst` holding
`src` XOR the keystream and everything else the caller can see as it was. -/
theorem bulk_correct (c : Call) (vaes : Bool) (hc : Pre c vaes)
    (hrsp : c.regs.rsp.toBitVec = c.rsp) (zmms : RegZmms) (flags : StatusFlags) :
    Reaches exe (Post c) (⟨c.regs, zmms, flags, c.mem⟩, 0x542a60) := by
  cases vaes
  · exact ni_correct c hc hrsp zmms flags
  · exact v_correct c hc hrsp zmms flags

end AesCtrX86
