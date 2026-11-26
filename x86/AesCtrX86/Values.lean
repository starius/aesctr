/-
What the code stores is `src ^^^ keystream`: the counter registers, the rounds
and the last round with the source folded into the round key.
-/
import AesCtrX86.Final
import AesCtrX86.Defs
import AesCtrX86.BitLemmas
import Kraken.X64.Ops.SimdInt

open BitVec

namespace AesCtrX86

/-! ## The counter -/

theorem ofNat128_eq_append (j : Nat) (hj : j < 2 ^ 64) :
    BitVec.ofNat 128 j = 0#64 ++ BitVec.ofNat 64 j := by
  apply BitVec.eq_of_toNat_eq
  have h128 : j < 2 ^ 128 := by omega
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt h128,
    Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]

theorem getLsbD_zero128 (i : Nat) : (0 : BitVec 128).getLsbD i = false := by simp

theorem getLsbD_ge64 (x : BitVec 64) (i : Nat) (h : 64 ≤ i) : x.getLsbD i = false :=
  BitVec.getLsbD_of_ge x i h

/-- `paddq` of `[j, 0]` to a counter register `[lo, hi]` adds `j` to `lo`. -/
theorem paddq_ctr (hi lo : BitVec 64) (j : Nat) (hj : j < 2 ^ 64) :
    SimdInt.paddq.interp (hi ++ lo) (BitVec.ofNat 128 j) = hi ++ (lo + BitVec.ofNat 64 j) := by
  rw [ofNat128_eq_append j hj]
  simp only [SimdInt.interp, BitVec.map2, BitVec.ofLanes, BitVec.lane, List.range,
    List.range.loop, List.foldl, Nat.reduceDiv, Nat.zero_mul, Nat.one_mul,
    extractLsb'_append_eq_right, extractLsb'_append_eq_left, BitVec.add_zero]
  generalize lo + BitVec.ofNat 64 j = x
  apply ext128
  simp (config := { maxSteps := 10000000, decide := true }) only [List.range, List.range.loop,
    List.forall_mem_cons, forall_mem_nil', and_true, getLsbD_append_64_64, BitVec.getLsbD_or,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero, getLsbD_zero128,
    getLsbD_ge64, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
    Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or, ↓reduceIte, Nat.reduceSub,
    Nat.reduceAdd, Nat.reduceLT, _root_.and_self, true_and, and_true]

/-- Without a wrap of the low 64 bits, `[lo + j, hi]` is the 128-bit counter plus `j`. -/
theorem ctr_add (hi lo : BitVec 64) (j : Nat) (h : lo.toNat + j < 2 ^ 64) :
    hi ++ (lo + BitVec.ofNat 64 j) = (hi ++ lo) + BitVec.ofNat 128 j := by
  apply BitVec.eq_of_toNat_eq
  have hlo : (lo + BitVec.ofNat 64 j).toNat = lo.toNat + j := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega)]
    exact Nat.mod_eq_of_lt h
  have hhi := hi.isLt
  have hlo2 := lo.isLt
  rw [BitVec.toNat_append, hlo, BitVec.toNat_add, BitVec.toNat_append, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show j < 2 ^ 128 by omega),
    ← Nat.shiftLeft_add_eq_or_of_lt (show lo.toNat + j < 2 ^ 64 by omega),
    ← Nat.shiftLeft_add_eq_or_of_lt hlo2, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## The rounds -/

/-- `r` rounds of `aesenc` with round keys `rk 1 .. rk r`, as the code runs them. -/
def encRounds (rk : Nat → BitVec 128) (x : BitVec 128) : Nat → BitVec 128
  | 0 => x
  | r + 1 => SimdCrypto.aesenc.interp (encRounds rk x r) (rk (r + 1))

theorem encRounds_eq (rk : Nat → BitVec 128) (x : BitVec 128) (r : Nat) :
    encRounds rk (x ^^^ rk 0) r = aesState rk x r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [encRounds, ih, aesenc_eq, aesState]

/-- What the code computes for block `j`: the counter block of counter `j`
through round 0, `nr - 1` rounds of `aesenc`, and `aesenclast` with the source
block XORed into the last round key, is block `j` of the output. -/
theorem out_eq (c : Call) (j : Nat) (hj : c.ivlo.toNat + j < 2 ^ 64) :
    SimdCrypto.aesenclast.interp
      (encRounds c.rk (SimdShuf.pshufb.interp (c.ivhi ++ (c.ivlo + BitVec.ofNat 64 j))
        5233100606242806050955395731361295#128 ^^^ c.rk 0) (c.nr - 1))
      (c.srcb j ^^^ c.rk c.nr) = c.out j := by
  rw [pshufb_bswap, encRounds_eq, aesenclast_eq, ctr_add _ _ _ hj]
  simp only [Call.out, keystream, aesEncrypt]
  ac_rfl

end AesCtrX86
