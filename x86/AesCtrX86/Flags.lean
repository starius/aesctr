/-
`cmp` and `sub` of small values: the result and the flags the conditional jumps
read, without unfolding Kraken's flag computation.
-/
import Kraken.X64.Semantics

namespace AesCtrX86

theorem subFlags_fst {w : Nat} (st : StatusFlags) (a b : BitVec w) :
    (subFlags st a b).fst = a - b := by
  simp [subFlags]

theorem addFlags_fst {w : Nat} (st : StatusFlags) (a b : BitVec w) :
    (addFlags st a b).fst = a + b := by
  simp [addFlags]

theorem ofNat_sub_ofNat (x k : Nat) (hk : k ≤ x) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 k = BitVec.ofNat 64 (x - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show x - k < 2 ^ 64 by omega),
    show 2 ^ 64 - k + x = (x - k) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (show x - k < 2 ^ 64 by omega)]

theorem sub_zero_lit {w : Nat} (x : BitVec w) : x - (0 : BitVec w) = x := BitVec.sub_zero x

theorem toNat_ofNat_sub (x k : Nat) (hx : x < 2 ^ 64) (hk : k < 2 ^ 64) :
    (BitVec.ofNat 64 x - BitVec.ofNat 64 k).toNat = (2 ^ 64 - k + x) % 2 ^ 64 := by
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hk]

/-- The carry flag of `cmp $k, x` (unsigned `x < k`). -/
theorem subFlags_cf (st : StatusFlags) (x k : Nat) (hx : x < 2 ^ 64) (hk : k < 2 ^ 64) :
    (subFlags st (BitVec.ofNat 64 x) (BitVec.ofNat 64 k)).snd.cf = decide (x < k) := by
  simp only [subFlags, StatusFlags.from_result, BitVec.unsigned, Bool.false_eq_true,
    ↓reduceIte, BitVec.sub_zero, sub_zero_lit, Int.sub_zero]
  rw [Bool.eq_iff_iff, bne_iff_ne, ne_eq, decide_eq_true_iff, toNat_ofNat_sub x k hx hk,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hk]
  constructor
  · intro h
    by_cases hge : x < k
    · exact hge
    · exfalso
      apply h
      rw [show 2 ^ 64 - k + x = (x - k) + 2 ^ 64 by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show x - k < 2 ^ 64 by omega)]
      omega
  · intro h heq
    rw [Nat.mod_eq_of_lt (show 2 ^ 64 - k + x < 2 ^ 64 by omega)] at heq
    omega

/-- The zero flag of `cmp $k, x` (`x = k`). -/
theorem subFlags_zf (st : StatusFlags) (x k : Nat) (hx : x < 2 ^ 64) (hk : k < 2 ^ 64) :
    (subFlags st (BitVec.ofNat 64 x) (BitVec.ofNat 64 k)).snd.zf = decide (x = k) := by
  simp only [subFlags, StatusFlags.from_result, Bool.false_eq_true, ↓reduceIte,
    BitVec.sub_zero, sub_zero_lit]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have h1 := congrArg BitVec.toNat h
    rw [toNat_ofNat_sub x k hx hk] at h1
    simp only [BitVec.zero, BitVec.toNat_ofNatLT] at h1
    by_cases hkx : k ≤ x
    · rw [show 2 ^ 64 - k + x = (x - k) + 2 ^ 64 by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (show x - k < 2 ^ 64 by omega)] at h1
      omega
    · rw [Nat.mod_eq_of_lt (show 2 ^ 64 - k + x < 2 ^ 64 by omega)] at h1
      omega
  · intro h
    subst h
    simp [BitVec.sub_self]

end AesCtrX86
