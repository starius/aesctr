/-
Lemmas and tactics shared by the generated proofs. Everything here is proved
from Lean's standard axioms (no `bv_decide`, no `native_decide`).
-/
import Arm.State
import Arm.Memory.Separate
import Arm.Memory.MemoryProofs
import Arm.Insts.Common
import Arm.Insts.DPSFP.Advanced_simd_three_same
import Arm.Insts.DPSFP.Advanced_simd_two_reg_misc
import AesCtr.Spec
import AesCtr.Lemmas

namespace AesCtr

open BitVec

/-! ## Memory: reads over writes, with plain linear side conditions -/

theorem rd16_write_same (x : BitVec 64) (v : BitVec 128) (m : Memory) (hx : x.toNat + 16 ≤ 2 ^ 64) :
    Memory.read_bytes 16 x (Memory.write_bytes 16 x v m) = v := by
  have hsub : mem_subset' x 16 x 16 := ⟨hx, hx, BitVec.le_refl x, Nat.le_refl _⟩
  rw [Memory.read_bytes_write_bytes_eq_of_mem_subset' hsub, Nat.sub_self]
  exact BitVec.extractLsb'_eq_self

theorem rd_write_sep {x : BitVec 64} {n : Nat} {y : BitVec 64} {v : BitVec 128} {m : Memory}
    (h : mem_separate' x n y 16) :
    Memory.read_bytes n x (Memory.write_bytes 16 y v m) = Memory.read_bytes n x m :=
  Memory.read_bytes_write_bytes_eq_read_bytes_of_mem_separate' h v

/-- Closes address side conditions (`mem_separate'`, `mem_legal'`, bounds) from
the `toNat` facts in the local context, with `omega`. -/
macro "mem_tac" : tactic => `(tactic| (
  first
  | (refine ⟨?_, ?_, ?_⟩ <;> (try unfold mem_legal') <;>
      (try simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]) <;>
      omega)
  | ((try unfold mem_legal') <;>
      (try simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]) <;>
      omega)))

/-! ## Counters -/


/-- `ADDS`/`ADC` result. -/
theorem awc_fst (x y : BitVec 64) (c : BitVec 1) :
    (AddWithCarry x y c).fst = x + y + setWidth 64 c := by
  apply BitVec.eq_of_toNat_eq
  simp only [AddWithCarry, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.zeroExtend_eq_setWidth]
  have := x.isLt; have := y.isLt; have := c.isLt
  simp only [Nat.reducePow, Nat.reduceAdd] at *
  omega

/-- `ADDS` carry flag. -/
theorem awc_c (x y : BitVec 64) (c : BitVec 1) :
    (AddWithCarry x y c).snd.c = if x.toNat + y.toNat + c.toNat < 2 ^ 64 then 0#1 else 1#1 := by
  simp only [AddWithCarry, make_pstate, BitVec.zeroExtend_eq_setWidth]
  have := x.isLt; have := y.isLt; have := c.isLt
  by_cases h : x.toNat + y.toNat + c.toNat < 2 ^ 64
  · rw [if_pos h, if_pos]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, Nat.reducePow, Nat.reduceAdd] at *
    omega
  · rw [if_neg h, if_neg]
    intro heq
    have := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, Nat.reducePow, Nat.reduceAdd] at *
    omega

/-- A 128-bit value made of two 64-bit halves. -/
theorem append_toNat (a b : BitVec 64) : (a ++ b : BitVec 128).toNat = a.toNat * 2 ^ 64 + b.toNat := by
  have h : (a ++ b : BitVec 128).toNat = (a ++ b).toNat := rfl
  rw [h, BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]

/-- One step of the scalar 128-bit counter increment `ADDS lo, lo, #1; ADC hi, hi, xzr`. -/
theorem add128_step (hi lo : BitVec 64) :
    (hi ++ lo) + 1#128 =
      (AddWithCarry hi 0#64 (AddWithCarry lo 1#64 0#1).snd.c).fst ++ (AddWithCarry lo 1#64 0#1).fst := by
  rw [awc_fst, awc_fst, awc_c]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, append_toNat, append_toNat]
  have hlo := lo.isLt
  have hhi := hi.isLt
  by_cases h : lo.toNat + (1#64).toNat + (0#1).toNat < 2 ^ 64
  · rw [if_pos h]
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod] at *
    omega
  · rw [if_neg h]
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod] at *
    omega
/-- `x + (i + 1) = (x + i) + 1`, to peel counter offsets one step at a time. -/
theorem add_ofNat_succ (x : BitVec 128) (i : Nat) :
    x + BitVec.ofNat 128 (i + 1) = (x + BitVec.ofNat 128 i) + 1#128 := by
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

end AesCtr

namespace AesCtr

/-- One scalar counter step, as `ADDS lo, lo, #1; ADC hi, hi, xzr` compute it. -/
def stepCtr (p : BitVec 64 × BitVec 64) : BitVec 64 × BitVec 64 :=
  ((AddWithCarry p.1 0#64 (AddWithCarry p.2 1#64 0#1).snd.c).fst, (AddWithCarry p.2 1#64 0#1).fst)

/-- `k` scalar counter steps from `(hi, lo)`. -/
def ctrN (hi lo : BitVec 64) : Nat → BitVec 64 × BitVec 64
  | 0 => (hi, lo)
  | k + 1 => stepCtr (ctrN hi lo k)

theorem ctrN_eq (hi lo : BitVec 64) (k : Nat) :
    (hi ++ lo) + BitVec.ofNat 128 k = (ctrN hi lo k).1 ++ (ctrN hi lo k).2 := by
  induction k with
  | zero => simp [ctrN]
  | succ k ih =>
    rw [add_ofNat_succ, ih, add128_step]
    rfl

end AesCtr

namespace AesCtr

theorem write_mem_bytes_mem (n : Nat) (addr : BitVec 64) (val : BitVec (n * 8)) (s : ArmState) :
    (write_mem_bytes n addr val s).mem = Memory.write_bytes n addr val s.mem := by
  rw [Memory.write_mem_bytes_eq_mem_write_bytes]

end AesCtr

/-- Run a tactic without Lean's error recovery, so that a failure is an
exception (and, as a `simp` discharger, a failed side condition) instead of a
logged error and a `sorry`. -/
elab "no_recover " t:tactic : tactic => Lean.Elab.Tactic.withoutRecover (Lean.Elab.Tactic.evalTactic t)

namespace AesCtr

open BitVec

/-- `ADD Vd.2D, Vn.2D, Vm.2D` on two halves. -/
theorem vadd2d_append (a1 a0 b1 b0 : BitVec 64) :
    DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (a1 ++ a0) (b1 ++ b0) 0#128 = (a1 + b1) ++ (a0 + b0) := by
  rw [DPSFP.binary_vector_op_aux_of_lt (by decide), DPSFP.binary_vector_op_aux_of_lt (by decide),
    DPSFP.binary_vector_op_aux_of_not_lt (by decide)]
  simp only [elem_get, elem_set, Nat.zero_mul, Nat.one_mul, Nat.zero_add]
  have e0 : BitVec.extractLsb' 0 64 (a1 ++ a0) = a0 := BitVec.extractLsb'_append_eq_right
  have e1 : BitVec.extractLsb' 64 64 (a1 ++ a0) = a1 := BitVec.extractLsb'_append_eq_left
  have f0 : BitVec.extractLsb' 0 64 (b1 ++ b0) = b0 := BitVec.extractLsb'_append_eq_right
  have f1 : BitVec.extractLsb' 64 64 (b1 ++ b0) = b1 := BitVec.extractLsb'_append_eq_left
  rw [e0, e1, f0, f1]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.partInstall, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_append, BitVec.truncate_eq_setWidth, hi, decide_true, BitVec.getLsbD_zero]
  by_cases h : i < 64
  · simp [h, hi]
  · simp [h, hi, show i - 64 < 64 by omega, show i - 64 < 128 by omega,
      BitVec.getLsbD_of_ge (a0 + b0) i (by omega)]

/-- `REV64 Vd.16B` on two halves. -/
theorem vrev128_64_8_append (a b : BitVec 64) :
    DPSFP.vrev128_64_8 (a ++ b) = bswap64 a ++ bswap64 b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [← rev_vector_64 a (by decide) (by decide) (by decide) (by decide) (by decide),
    ← rev_vector_64 b (by decide) (by decide) (by decide) (by decide) (by decide)]
  unfold DPSFP.vrev128_64_8 rev_vector
  simp only [show ¬ (64 = 128) by decide, dite_false]
  unfold rev_vector
  simp only [dite_true, BitVec.getLsbD_cast, BitVec.getLsbD_append]
  by_cases h : i < 64
  · simp only [h, ite_true]
    rw [getLsbD_rev_elems_8 64 _ _ _ i h, getLsbD_rev_elems_8 64 _ _ _ i h]
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_cast]
    have : (64 / 8 - 1 - i / 8) * 8 + i % 8 < 64 := by omega
    simp [this]
  · simp only [h, ite_false]
    rw [getLsbD_rev_elems_8 64 _ _ _ (i - 64) (by omega), getLsbD_rev_elems_8 64 _ _ _ (i - 64) (by omega)]
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_append, BitVec.getLsbD_cast,
      BitVec.getLsbD_ushiftRight]
    have : (64 / 8 - 1 - (i - 64) / 8) * 8 + (i - 64) % 8 < 64 := by omega
    simp [this, show ¬ (64 + ((64 / 8 - 1 - (i - 64) / 8) * 8 + (i - 64) % 8) < 64) by omega]

/-- Adding `x` to the counter `hi * 2^64 + lo` when the low half does not wrap. -/
theorem ctr_nocarry (hi lo : BitVec 64) (x : Nat) (h : lo.toNat + x < 2 ^ 64) :
    (hi ++ lo) + BitVec.ofNat 128 x = hi ++ (lo + BitVec.ofNat 64 x) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, append_toNat, append_toNat, BitVec.toNat_add]
  simp only [BitVec.toNat_ofNat]
  have hx : x < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt (show x < 2 ^ 128 by omega), Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt h]
  have := hi.isLt
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

end AesCtr

namespace AesCtr

theorem ofNat_add_64 (a b : Nat) :
    BitVec.ofNat 64 (a + b) = BitVec.ofNat 64 a + BitVec.ofNat 64 b := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, Nat.add_mod]

theorem mul_add_ofNat_64 (m k : Nat) :
    BitVec.ofNat 64 (16 * (m + k)) = BitVec.ofNat 64 (16 * m) + BitVec.ofNat 64 (16 * k) := by
  rw [Nat.mul_add, ofNat_add_64]

end AesCtr

namespace AesCtr

/-- The plain path's final XORs, `src ^^^ (lastKey ^^^ state)`, in the spec's order. -/
theorem xor_plain (x k s : BitVec 128) : x ^^^ (k ^^^ s) = x ^^^ (s ^^^ k) := by
  rw [BitVec.xor_comm k s]

/-- The EOR3 path's final XOR, `(src ^^^ state) ^^^ lastKey`, in the spec's order. -/
theorem xor_eor3 (x s k : BitVec 128) : (x ^^^ s) ^^^ k = x ^^^ (s ^^^ k) := by
  rw [BitVec.xor_assoc]

end AesCtr

namespace AesCtr

/-- `ADD` of the increment register `[0, 1]`, which `simp` folds into the literal `2^64`. -/
theorem vadd2d_one (a1 a0 : BitVec 64) :
    DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (a1 ++ a0) 18446744073709551616#128 0#128 =
      (a1 + 1#64) ++ a0 := by
  rw [show (18446744073709551616#128 : BitVec 128) = 1#64 ++ 0#64 by decide, vadd2d_append,
    BitVec.add_zero]

/-- `ADD` of the increment register `[0, 2]` (the literal `2^65`). -/
theorem vadd2d_two (a1 a0 : BitVec 64) :
    DPSFP.binary_vector_op_aux 0 2 64 BitVec.add (a1 ++ a0) 36893488147419103232#128 0#128 =
      (a1 + 2#64) ++ a0 := by
  rw [show (36893488147419103232#128 : BitVec 128) = 2#64 ++ 0#64 by decide, vadd2d_append,
    BitVec.add_zero]

end AesCtr

namespace AesCtr

/-- `INS Vd.D[0], hi; INS Vd.D[1], lo` builds `lo ++ hi`. -/
theorem partInstall_hi_lo (a b : BitVec 64) (x : BitVec 128) :
    BitVec.partInstall 64 64 b (BitVec.partInstall 0 64 a x) = b ++ a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.partInstall, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_append, BitVec.truncate_eq_setWidth, hi, decide_true]
  by_cases h : i < 64
  · simp [h, hi]
  · simp [h, hi, show i - 64 < 64 by omega, show i - 64 < 128 by omega,
      BitVec.getLsbD_of_ge a i (by omega)]

/-- The increment register `[0, 1]`: `EOR V, V, V` then `INS V.D[1], 1`. -/
theorem partInstall_one (x : BitVec 128) :
    BitVec.partInstall 64 64 1#64 (x ^^^ x) = 1#64 ++ 0#64 := by
  rw [BitVec.xor_self]; decide

end AesCtr
