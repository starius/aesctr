/-
Kraken's AES round instructions are the FIPS-197 rounds of the spec.

The model of `aesenc` and `aesenclast` (Kraken.X64.Ops.SimdCrypto, from Craig
Tiller's fork) has its own S-box table and GF(2^8) multiplication. These
lemmas show that, on one 128-bit lane, they compute the spec's round
(LNSym's SubBytes, ShiftRows and MixColumns) and last round.
-/
import AesCtrX86.Spec
import AesCtrX86.BitLemmas
import Kraken.X64.Ops.SimdCrypto

open BitVec

namespace AesCtrX86

/-- LNSym's S-box lookup, as `SubBytes` does it. -/
def lnsymSbox (x : BitVec 8) : BitVec 8 := extractLsb' (x.toNat * 8) 8 (LNSym.flatten LNSym.SBOX)

theorem lnsymSbox_def (x : BitVec 8) :
    extractLsb' (x.toNat * 8) 8 (LNSym.flatten LNSym.SBOX) = lnsymSbox x := rfl

/-- Multiplication by 2 in GF(2^8). -/
def xtime (x : BitVec 8) : BitVec 8 := (x <<< 1) ^^^ (if x.msb then 0x1b#8 else 0#8)

/-! The tables agree on all 256 bytes (checked by the kernel). -/

theorem sbox_aux : ∀ n, n < 256 → aesSbox.getD n 0 = lnsymSbox (BitVec.ofNat 8 n) := by
  decide +kernel
theorem ff02_aux : ∀ n, n < 256 → LNSym.FFmul02 (BitVec.ofNat 8 n) = xtime (BitVec.ofNat 8 n) := by
  decide +kernel
theorem ff03_aux : ∀ n, n < 256 →
    LNSym.FFmul03 (BitVec.ofNat 8 n) = xtime (BitVec.ofNat 8 n) ^^^ BitVec.ofNat 8 n := by
  decide +kernel
theorem gf1_aux : ∀ n, n < 256 → gf2p8Mul 1 (BitVec.ofNat 8 n) = BitVec.ofNat 8 n := by
  decide +kernel
theorem gf2_aux : ∀ n, n < 256 → gf2p8Mul 2 (BitVec.ofNat 8 n) = xtime (BitVec.ofNat 8 n) := by
  decide +kernel
theorem gf3_aux : ∀ n, n < 256 →
    gf2p8Mul 3 (BitVec.ofNat 8 n) = xtime (BitVec.ofNat 8 n) ^^^ BitVec.ofNat 8 n := by
  decide +kernel

theorem ofNat_toNat8 (x : BitVec 8) : BitVec.ofNat 8 x.toNat = x := by simp

theorem sbox_eq (x : BitVec 8) : aesSbox.getD x.toNat 0 = lnsymSbox x := by
  simpa [ofNat_toNat8] using sbox_aux x.toNat x.isLt
theorem ff02_eq (x : BitVec 8) : LNSym.FFmul02 x = xtime x := by
  simpa [ofNat_toNat8] using ff02_aux x.toNat x.isLt
theorem ff03_eq (x : BitVec 8) : LNSym.FFmul03 x = xtime x ^^^ x := by
  simpa [ofNat_toNat8] using ff03_aux x.toNat x.isLt
theorem gf1_eq (x : BitVec 8) : gf2p8Mul 1#8 x = x := by
  simpa [ofNat_toNat8] using gf1_aux x.toNat x.isLt
theorem gf2_eq (x : BitVec 8) : gf2p8Mul 2#8 x = xtime x := by
  simpa [ofNat_toNat8] using gf2_aux x.toNat x.isLt
theorem gf3_eq (x : BitVec 8) : gf2p8Mul 3#8 x = xtime x ^^^ x := by
  simpa [ofNat_toNat8] using gf3_aux x.toNat x.isLt

/-! The round functions -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Both sides, bit by bit: each bit is an XOR of bits of `v`, in a different
order on each side. -/
theorem mixColumns_eq (v : BitVec 128) : aesMixColumns v = MixColumns v := by
  conv => lhs; simp [aesMixColumns, aesMix, BitVec.ofLanes, BitVec.lane, List.range,
    List.range.loop, gf1_eq, gf2_eq, gf3_eq]
  conv => rhs; simp only [MixColumns, LNSym.AESMixColumns, LNSym.MixColumns,
    LNSym.MixColumns_aux, ff02_eq, ff03_eq, LNSym.partInstall, Nat.reduceSub, Nat.reduceMul]
  apply ext128
  simp only [List.range, List.range.loop, List.forall_mem_cons, forall_mem_nil', and_true]
  -- The 16-byte output concatenation.
  simp (config := { decide := true }) only [getLsbD_append_top32,
    BitVec.getLsbD_append, Nat.reduceLT, Nat.reduceSub, ↓reduceIte, ite_true, ite_false]
  -- Bits through `xtime` and the 4-byte column inputs, before any width folding.
  simp (config := { maxSteps := 10000000, decide := true }) only [xtime,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor,
    BitVec.getLsbD_not, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes, BitVec.getLsbD_zero,
    BitVec.reduceGetLsb, BitVec.msb_eq_getLsbD_last, getLsbD_append_top32,
    BitVec.getLsbD_append, decide_true, decide_false, Bool.true_and, Bool.false_and,
    Bool.and_true, Bool.and_false, Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or,
    Bool.true_or, Bool.or_true, ite_true, ite_false, ↓reduceIte, Nat.reduceSub, Nat.reduceMul,
    Bool.false_eq_true, getLsbD_ite', ite_true_false_bool, ite_self, Bool.false_xor,
    Bool.xor_false]
  -- Index arithmetic.
  simp (config := { maxSteps := 10000000, decide := true }) only [
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor,
    BitVec.getLsbD_not, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes, BitVec.getLsbD_zero,
    BitVec.reduceGetLsb, Nat.reduceLT, Nat.reduceLeDiff, decide_true,
    decide_false, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.not_true,
    Bool.not_false, Bool.or_false, Bool.false_or, Bool.true_or, Bool.or_true, ite_true,
    ite_false, ↓reduceIte, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv,
    Nat.reduceMod, Bool.false_eq_true, and_true, true_and, getLsbD_ite',
    ite_true_false_bool, ite_self, Bool.false_xor, Bool.xor_false, getLsbD_ge8]
  -- XOR chains of single bits of `v`, in different orders.
  simp only [Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm, and_true, true_and,
    _root_.and_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Both sides, bit by bit: each bit is a bit of an S-box output. -/
theorem shiftRowsSubBytes_eq (a : BitVec 128) :
    aesShiftRowsSubBytes a = ShiftRows (SubBytes a) := by
  conv => lhs; simp only [aesShiftRowsSubBytes, aesPermuteSub, sbox_eq]
  conv => lhs; simp only [BitVec.ofLanes, BitVec.lane, List.range, List.range.loop, List.foldl,
    List.size_toArray, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd, Nat.reduceLT,
    getElem!_pos, List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero, Nat.reduceMul]
  conv => rhs; simp only [ShiftRows, LNSym.ShiftRows, SubBytes, LNSym.SubBytes, LNSym.SubBytes_aux,
    lnsymSbox_def, LNSym.partInstall]
  apply ext128
  simp only [List.range, List.range.loop, List.forall_mem_cons, forall_mem_nil', and_true]
  -- The 16-byte `ShiftRows` concatenation, before any width folding.
  simp (config := { decide := true }) only [BitVec.getLsbD_append,
    Nat.reduceLT, Nat.reduceSub, ↓reduceIte, ite_true, ite_false]
  simp (config := { maxSteps := 10000000, decide := true }) only [
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor,
    BitVec.getLsbD_not, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes, BitVec.getLsbD_cast, BitVec.getLsbD_zero,
    BitVec.getLsbD_ushiftRight, BitVec.reduceGetLsb, BitVec.reduceExtractLsb', BitVec.reduceAnd,
    BitVec.reduceToNat, BitVec.msb_eq_getLsbD_last, Nat.reduceLT, Nat.reduceLeDiff, decide_true,
    decide_false, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.not_true,
    Bool.not_false, Bool.or_false, Bool.false_or, Bool.true_or, Bool.or_true, ite_true,
    ite_false, ↓reduceIte, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv,
    Nat.reduceMod, Bool.false_eq_true, and_true, true_and, BitVec.zero_eq, getLsbD_ge8]

/-- `aesenc` on one lane: the state `a` goes through one FIPS-197 round with
round key `b`. -/
theorem aesenc_eq (a b : BitVec 128) :
    SimdCrypto.interp .aesenc a b = MixColumns (ShiftRows (SubBytes a)) ^^^ b := by
  simp only [SimdCrypto.interp, shiftRowsSubBytes_eq, mixColumns_eq]

/-- `aesenclast` on one lane: the last round, which has no MixColumns. -/
theorem aesenclast_eq (a b : BitVec 128) :
    SimdCrypto.interp .aesenclast a b = ShiftRows (SubBytes a) ^^^ b := by
  simp only [SimdCrypto.interp, shiftRowsSubBytes_eq]

end AesCtrX86
