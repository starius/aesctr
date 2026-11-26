/-
The two ends of the VAES path of `ctrBlocksBulkAsm`: the entry code, up to
the loop or the tail, and `vzeroupper; ret`.
-/
import AesCtrX86.NIEnds
import AesCtrX86.VState

open Std Std.ExtHashMap

namespace AesCtrX86

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

/-- The entry with `vaes = true`: the arguments and the VAES flag as on the
AES-NI path, then the counter and mask registers in both lanes, then the tail
if `n < 16` and the loop otherwise. -/
theorem v_entry (c : Call) (hc : Pre c true) (hrsp : c.regs.rsp.toBitVec = c.rsp)
    (Q : MachineState → Prop) (zmms : RegZmms) (flags : StatusFlags)
    (ktail : ∀ s', VRegs c 0 s' → s'.regs.rdi.toBitVec = BitVec.ofNat 64 c.n → c.n < 16 →
      Runs exe Q (s', 0x543829))
    (kloop : ∀ s', VRegs c 0 s' → s'.regs.rdi.toBitVec = BitVec.ofNat 64 (c.n - 0) →
      BitVec.setWidth 256 s'.zmms.zmm11 = 16#128 ++ 16#128 → 0 + 16 ≤ c.n →
      Runs exe Q (s', 0x543469)) :
    Runs exe Q (⟨c.regs, zmms, flags, c.mem⟩, 0x542a80) := by
  have hn64 : c.n < 2 ^ 64 := by have := hc.src_fit; omega
  have hmask : Mem.loadInt c.mem 5621904#64 16 = some (maskVal.toNat : Int) := hc.mask
  have hoff16 : Mem.loadInt c.mem 5622336#64 16 = some 16 := by
    have := hc.offs 16 (by omega)
    simpa [Holds, offAddr] using this
  have hvaes := hc.arg_vaes
  simp only [↓reduceIte] at hvaes
  rw [runs_def, next_542a80]
  simp only [blk_542a80]
  xstep [hrsp, hc.arg_nr, hc.arg_xk, hc.arg_dst, hc.arg_src, hc.arg_n, hc.arg_ivlo, hc.arg_ivhi,
    hvaes, hn64, ofInt_natCast64, label_542f49, label_54343c]
  intro v
  apply reaches_of_runs
  rw [runs_def, next_54343c]
  simp only [blk_54343c]
  vstep [hmask, hoff16, hn64, label_543829, BitVec.setWidth_setWidth_of_le]
  by_cases hsmall : c.n < 16
  · simp only [hsmall, decide_true, ite_true, Effects.All]
    apply reaches_of_runs
    refine ktail _ ⟨rfl, rfl, by simp [blockAddr_zero], by simp [blockAddr_zero], rfl, rfl, rfl,
      rfl, ?_, by simp [setWidth_256_512, maskVal], memInv_zero c⟩ rfl hsmall
    simp only [setWidth_256_512, ctr_lanes']
    simp
  · simp only [hsmall, decide_false, Bool.false_eq_true, ite_false]
    vstep [hoff16]
    rw [← runs_def]
    refine kloop _ ⟨rfl, rfl, by simp [blockAddr_zero], by simp [blockAddr_zero], rfl, rfl, rfl,
      rfl, ?_, by simp [setWidth_256_512, maskVal], memInv_zero c⟩ (by simp) ?_ (by omega)
    · simp only [setWidth_256_512, ctr_lanes']
      simp
    · simp

/-- `vzeroupper; ret` at the end of the VAES path. -/
theorem v_ret (c : Call) (v : Bool) (hc : Pre c v) (hrsp : c.regs.rsp.toBitVec = c.rsp)
    (s : MachineData) (hs : NIFinal c c.n s) :
    Runs exe (Post c) (s, 0x543d72) := by
  have hra : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (c.ra.toNat : Int) := by
    rw [hs.rsp, hrsp, loadInt_frame hs.mem _ 8 (fun t ht hin => by
      apply hc.sep_stack _ hin
      rw [inR_iff _ _ _ (by have := hc.rsp_fit; omega),
        toNat_add_of_lt _ _ (by have := hc.rsp_fit; omega)]
      omega)]
    exact hc.ret
  rw [runs_def, next_543d72]
  simp only [blk_543d72]
  xstep [hra]
  exact reaches_done ⟨by simp, by simp [hs.rsp, hrsp], hs.rbp, hs.r14, hs.r15, hs.mem⟩

end AesCtrX86
