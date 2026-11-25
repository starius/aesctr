/-
Bit-level facts the generated proofs use. Everything here is proved from
Lean's standard axioms (no `bv_decide`, no `native_decide`).
-/
import Arm.State
import Arm.Insts.Common
import AesCtr.Spec

namespace AesCtr

open BitVec

/-- Two `INS` (general) instructions writing both halves of a vector register. -/
theorem partInstall_lo_hi (a b : BitVec 64) (x : BitVec 128) :
    BitVec.partInstall 0 64 a (BitVec.partInstall 64 64 b x) = b ++ a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.partInstall, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes,
    BitVec.getLsbD_append, BitVec.truncate_eq_setWidth, hi, decide_true]
  by_cases h : i < 64
  · simp [h, hi]
  · simp [h, hi, show i - 64 < 64 by omega, show i - 64 < 128 by omega,
      BitVec.getLsbD_of_ge a i (by omega)]

theorem getLsbD_rev_elems_8 : ∀ (n : Nat) (x : BitVec n) (h0 : 8 ∣ n) (h1 : 0 < 8) (i : Nat),
    i < n → (rev_elems n 8 x h0 h1).getLsbD i = x.getLsbD ((n / 8 - 1 - i / 8) * 8 + i % 8) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro x h0 h1 i hi
    by_cases hn : n ≤ 8
    · rw [rev_elems]
      simp only [hn, dite_true]
      congr 1
      omega
    · rw [rev_elems_step x h0 h1 hn]
      simp only [BitVec.getLsbD_cast, BitVec.getLsbD_append]
      by_cases hlt : i < n - 8
      · simp only [hlt, ite_true]
        rw [ih (n - 8) (by omega) _ _ h1 i hlt]
        simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
        have h8 : 8 ∣ n - 8 := Nat.dvd_sub h0 (Nat.dvd_refl 8)
        rw [decide_eq_true (by omega), Bool.true_and]
        congr 1
        omega
      · simp only [hlt, ite_false, BitVec.getLsbD_setWidth]
        rw [decide_eq_true (by omega), Bool.true_and]
        congr 1
        omega

theorem rev_vector_64 (x : BitVec 64) (h0 h1 h2 h3 h4) :
    rev_vector 64 64 8 x h0 h1 h2 h3 h4 = bswap64 x := by
  unfold rev_vector
  simp only [dite_true]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_cast, getLsbD_rev_elems_8 64 _ h3 h0 i hi, BitVec.getLsbD_cast]
  simp only [bswap64, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  repeat' split
  all_goals first
    | omega
    | (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega)

def srPerm (j : Nat) : Nat := (j + 4 * (j % 4)) % 16

/-- Byte `j` of a block. -/
abbrev byte (x : BitVec 128) (j : Nat) : BitVec 8 := x.extractLsb' (8 * j) 8

theorem byte_shiftRows (x : BitVec 128) (j : Nat) (hj : j < 16) :
    byte (AESCommon.ShiftRows x) j = byte x (srPerm j) := by
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
      j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [byte, srPerm, BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and,
      Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod]
    simp (disch := omega) only [AESCommon.ShiftRows, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb',
      if_pos, if_neg, decide_true, Bool.true_and]
    rw [decide_eq_true (by omega), Bool.true_and]
    apply congrArg

    omega

theorem eq_of_bytes {x y : BitVec 128} (h : ∀ j, j < 16 → byte x j = byte y j) : x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := congrArg (fun b => b.getLsbD (i % 8)) (h (i / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb'] at this
  rw [show 8 * (i / 8) + i % 8 = i by omega] at this
  simpa [show i % 8 < 8 by omega] using this

/-- The AES S-box. -/
def sbox (b : BitVec 8) : BitVec 8 :=
  (BitVec.flatten AESCommon.SBOX).extractLsb' (b.toNat * 8) 8

theorem byte_subBytes_aux (op : BitVec 128) : ∀ (n : Nat) (out : BitVec 128) (j : Nat),
    n ≤ 16 → j < 16 →
    byte (AESCommon.SubBytes_aux n op out) j = if 16 - n ≤ j then sbox (byte op j) else byte out j := by
  intro n
  induction n with
  | zero =>
    intro out j _ hj
    simp only [AESCommon.SubBytes_aux]
    rw [if_neg (by omega)]
  | succ n ih =>
    intro out j hn hj
    simp only [AESCommon.SubBytes_aux]
    rw [ih _ j (by omega) hj]
    by_cases h1 : 16 - n ≤ j
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1]
      by_cases h2 : j = 15 - n
      · subst h2
        rw [if_pos (by omega)]
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp only [byte, sbox, BitVec.partInstall, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
          BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
          BitVec.getLsbD_allOnes, BitVec.truncate_eq_setWidth]
        have e : 16 - (n + 1) = 15 - n := by omega
        simp [e, hi, show i < 128 by omega, show 8 * (15 - n) + i < 128 by omega,
          show ¬ (8 * (15 - n) + i < 8 * (15 - n)) by omega,
          show 8 * (15 - n) + i - (15 - n) * 8 = i by omega, Nat.mul_comm]
      · rw [if_neg (by omega)]
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        simp only [byte, BitVec.partInstall, BitVec.getLsbD_extractLsb', BitVec.getLsbD_or,
          BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
          BitVec.getLsbD_allOnes, BitVec.truncate_eq_setWidth]
        have e : 16 - (n + 1) = 15 - n := by omega
        by_cases h3 : 8 * j + i < (15 - n) * 8
        · simp [e, hi, h3, show 8 * j + i < 128 by omega]
        · simp [e, hi, h3, show 8 * j + i < 128 by omega, show ¬ (8 * j + i - (15 - n) * 8 < 8) by omega]

theorem byte_subBytes (x : BitVec 128) (j : Nat) (hj : j < 16) :
    byte (AESCommon.SubBytes x) j = sbox (byte x j) := by
  simp only [AESCommon.SubBytes]
  rw [byte_subBytes_aux x 16 _ j (by omega) hj, if_pos (by omega)]

theorem srPerm_lt (j : Nat) : srPerm j < 16 := by simp only [srPerm]; omega

/-- SubBytes and ShiftRows commute (FIPS-197 notes this): SubBytes is byte-wise, ShiftRows
permutes bytes. -/
theorem subBytes_shiftRows (x : BitVec 128) :
    AESCommon.SubBytes (AESCommon.ShiftRows x) = AESCommon.ShiftRows (AESCommon.SubBytes x) := by
  apply eq_of_bytes
  intro j hj
  rw [byte_subBytes _ j hj, byte_shiftRows _ j hj, byte_shiftRows _ j hj,
    byte_subBytes _ _ (srPerm_lt j)]

end AesCtr

namespace AesCtr

/-- The counter block of `hi * 2^64 + lo`. -/
theorem counterBlock_append (hi lo : BitVec 64) :
    counterBlock (hi ++ lo) = bswap64 lo ++ bswap64 hi := by
  unfold counterBlock
  have h1 : BitVec.extractLsb' 0 64 (hi ++ lo) = lo := BitVec.extractLsb'_append_eq_right
  have h2 : BitVec.extractLsb' 64 64 (hi ++ lo) = hi := BitVec.extractLsb'_append_eq_left
  rw [h1, h2]

/-- The XORs at the end of a block: `(lastKey ^^^ state) ^^^ src`, the order the
assembly computes them, is `src ^^^ (state ^^^ lastKey)`, the spec's order. -/
theorem xor_final (k s src : BitVec 128) : (k ^^^ s) ^^^ src = src ^^^ (s ^^^ k) := by
  rw [BitVec.xor_comm k s, BitVec.xor_comm _ src]

end AesCtr
