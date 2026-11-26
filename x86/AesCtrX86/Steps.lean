/-
Lemmas for stepping through `exe` with `simp`: normal forms of Kraken's address
and register arithmetic, and of the vector register file.
-/
import AesCtrX86.Layout
import Std.Tactic.BVDecide
import Kraken.X64.OmniSemantics

open Std Std.ExtHashMap

namespace AesCtrX86

/-! ## Normal forms -/

theorem addr_reg (x : BitVec 64) (d : Int) :
    BitVec.zeroExtend 64 (BitVec.ofInt 64 (BitVec.signed x + 0 + d)) = x + BitVec.ofInt 64 d := by
  simp [BitVec.signed, BitVec.ofInt_add]

/-- The same, after `Int.add_zero` and `setWidth_eq` (simp works bottom-up). -/
theorem addr_reg' (x : BitVec 64) (d : Int) :
    BitVec.ofInt 64 (BitVec.signed x + d) = x + BitVec.ofInt 64 d := by
  simp [BitVec.signed, BitVec.ofInt_add]

theorem addr_reg0 (x : BitVec 64) : BitVec.ofInt 64 (BitVec.signed x) = x := by
  simp [BitVec.signed]

theorem ofInt_toNat (x : BitVec 64) : BitVec.ofInt 64 (x.toNat : Int) = x := by simp

theorem drop_zero (x : BitVec 64) : BitVec.drop x 0 = x := by simp [BitVec.drop]

/-! ## Vector registers -/

/-- Kraken's `take` is `setWidth`: the normal form used below. -/
theorem take_eq {w : Nat} (x : BitVec w) (n : Nat) : BitVec.take x n = x.setWidth n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.take, hi]

/-- Reading back the low `n` bits after a legacy SSE write. -/
theorem setWidth_replaceLow {w n : Nat} (x : BitVec w) (v : BitVec n) (h : n ≤ w) :
    (x.replaceLow v).setWidth n = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.replaceLow, BitVec.getLsbD_append, hi]
  omega

/-! Kraken's register values have type `ZmmValue`, a `def` for `BitVec 512` that
`simp` does not unfold, so the lemmas it uses on registers are stated for
`ZmmValue`. A second legacy write of the low 128 bits replaces the first, so a
register is never more than one write deep. -/

theorem take_eq_zmm (x : ZmmValue) (n : Nat) :
    @BitVec.take 512 x n = @BitVec.setWidth 512 n x :=
  take_eq (w := 512) x n

theorem setWidth_replaceLow_zmm (x : ZmmValue) (v : BitVec 128) :
    BitVec.setWidth 128 (@BitVec.replaceLow 512 128 x v) = v :=
  setWidth_replaceLow (w := 512) x v (by decide)

theorem replaceLow_replaceLow (x : BitVec 512) (u v : BitVec 128) :
    (x.replaceLow u).replaceLow v = x.replaceLow v := by
  simp only [BitVec.replaceLow]
  bv_normalize

theorem replaceLow_replaceLow_zmm (x : ZmmValue) (u v : BitVec 128) :
    @BitVec.replaceLow 512 128 (@BitVec.replaceLow 512 128 x u) v = @BitVec.replaceLow 512 128 x v :=
  replaceLow_replaceLow x u v

theorem ofInt_toNat128 (x : BitVec 128) : BitVec.ofInt 128 (x.toNat : Int) = x := by simp

theorem map2_128 (f : BitVec 128 → BitVec 128 → BitVec 128) (a b : BitVec 128) :
    BitVec.map2 128 f a b = f a b := by
  simp [BitVec.map2, BitVec.ofLanes, BitVec.lane, List.range, List.range.loop]

