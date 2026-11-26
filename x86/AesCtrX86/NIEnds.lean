/-
The two ends of the AES-NI path of `ctrBlocksBulkAsm`: the entry code, up to
the loop or the tail, and `ret`.
-/
import AesCtrX86.Tactic
import AesCtrX86.Reach
import AesCtrX86.NIState

open Std Std.ExtHashMap

namespace AesCtrX86

set_option maxHeartbeats 20000000
set_option maxRecDepth 100000

/-- `ret` at the end of the AES-NI path. -/
theorem ni_ret (c : Call) (v : Bool) (hc : Pre c v) (hrsp : c.regs.rsp.toBitVec = c.rsp)
    (s : MachineData) (hs : NIFinal c c.n s) :
    Runs exe (Post c) (s, 0x54343b) := by
  have hra : Mem.loadInt s.dmem s.regs.rsp.toBitVec 8 = some (c.ra.toNat : Int) := by
    rw [hs.rsp, hrsp, loadInt_frame hs.mem _ 8 (fun t ht hin => by
      apply hc.sep_stack _ hin
      rw [inR_iff _ _ _ (by have := hc.rsp_fit; omega),
        toNat_add_of_lt _ _ (by have := hc.rsp_fit; omega)]
      omega)]
    exact hc.ret
  rw [runs_def, next_54343b]
  simp only [blk_54343b]
  xstep [hra]
  exact reaches_done ⟨by simp, by simp [hs.rsp, hrsp], hs.rbp, hs.r14, hs.r15, hs.mem⟩

/-- The entry with `vaes = false`: the arguments, the VAES flag, the counter and
mask registers, then the tail if `n < 8` and the loop otherwise. -/
theorem ni_entry (c : Call) (hc : Pre c false) (hrsp : c.regs.rsp.toBitVec = c.rsp)
    (Q : MachineState → Prop) (zmms : RegZmms) (flags : StatusFlags)
    (ktail : ∀ s', NIRegs c 0 s' → s'.regs.rdi.toBitVec = BitVec.ofNat 64 c.n → c.n < 8 →
      Runs exe Q (s', 0x542f49))
    (kloop : ∀ s', NIRegs c 0 s' → s'.regs.rdi.toBitVec = BitVec.ofNat 64 (c.n - 0) →
      BitVec.setWidth 128 s'.zmms.zmm11 = BitVec.ofNat 128 8 → 0 + 8 ≤ c.n →
      Runs exe Q (s', 0x542ad9)) :
    Runs exe Q (⟨c.regs, zmms, flags, c.mem⟩, 0x542a80) := by
  have hn64 : c.n < 2 ^ 64 := by have := hc.src_fit; omega
  have hmask : Mem.loadInt c.mem 5621904#64 16 = some (maskVal.toNat : Int) := hc.mask
  have hoff8 : Mem.loadInt c.mem 5622208#64 16 = some 8 := by
    have := hc.offs 8 (by omega)
    simpa [Holds, offAddr] using this
  have hvaes := hc.arg_vaes
  simp only [Bool.false_eq_true, ↓reduceIte] at hvaes
  rw [runs_def, next_542a80]
  simp only [blk_542a80]
  xstep [hrsp, hc.arg_nr, hc.arg_xk, hc.arg_dst, hc.arg_src, hc.arg_n, hc.arg_ivlo, hc.arg_ivhi,
    hvaes, hmask, hoff8, hn64, ofInt_natCast64, label_542f49, label_54343c]
  intro v
  by_cases hsmall : c.n < 8
  · simp only [hsmall, decide_true, ite_true, Effects.All]
    apply reaches_of_runs
    refine ktail _ ⟨rfl, rfl, by simp [blockAddr_zero], by simp [blockAddr_zero], rfl, rfl, rfl,
      rfl, ?_, by simp [setWidth_replaceLow_zmm, maskVal], memInv_zero c⟩ rfl hsmall
    simp only [setWidth_replaceLow_zmm, ctr_lanes']
    simp
  · simp only [hsmall, decide_false, Bool.false_eq_true, ite_false]
    xstep [hoff8]
    rw [← runs_def]
    refine kloop _ ⟨rfl, rfl, by simp [blockAddr_zero], by simp [blockAddr_zero], rfl, rfl, rfl,
      rfl, ?_, by simp [setWidth_replaceLow_zmm, maskVal], memInv_zero c⟩ (by simp) ?_ (by omega)
    · simp only [setWidth_replaceLow_zmm, ctr_lanes']
      simp
    · simp only [setWidth_replaceLow_zmm]

end AesCtrX86
