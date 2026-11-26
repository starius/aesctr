/-
The counter in a register: `movq` and `pinsrq $1` put `[lo, hi]` in it
(`ctr_lanes`), and `pshufb` with `bswapMask` turns it into the counter block of
the spec (`pshufb_bswap`).
-/
import AesCtrX86.Round
import AesCtrX86.BitLemmas
import Kraken.X64.Ops.SimdShuf

open BitVec

namespace AesCtrX86

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `movq` then `pinsrq $1`: the counter register is `[lo, hi]`. -/
theorem ctr_lanes (lo hi : BitVec 64) :
    (BitVec.ofLanes 128 64 fun i =>
      if (i == 1 % (128 / 64)) = true then BitVec.extractLsb' 0 64 hi
      else BitVec.lane 64 i (BitVec.setWidth 128 lo)) = hi ++ lo := by
  apply ext128
  simp (config := { maxSteps := 10000000, decide := true }) only [BitVec.ofLanes, BitVec.lane,
    List.range, List.range.loop, List.foldl, List.forall_mem_cons, forall_mem_nil', and_true,
    getLsbD_append_64_64, BitVec.getLsbD_or, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero,
    BitVec.reduceGetLsb, decide_true, decide_false, Bool.true_and, Bool.false_and,
    Bool.and_true, Bool.and_false, Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or,
    Bool.or_true, ↓reduceIte, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv,
    Nat.reduceMod, Nat.reduceBEq, _root_.and_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- `pshufb` with `bswapMask` reverses the 16 bytes: the counter block. -/
theorem pshufb_bswap (x : BitVec 128) :
    SimdShuf.pshufb.interp x 5233100606242806050955395731361295#128 = counterBlock x := by
  apply ext128
  simp only [List.range, List.range.loop, List.forall_mem_cons, forall_mem_nil', and_true]
  -- The concatenations of `counterBlock` and `bswap64`, before any width folding.
  simp only [counterBlock, bswap64, getLsbD_append_64_64, getLsbD_append_bswap,
    BitVec.getLsbD_append, Nat.reduceLT, Nat.reduceSub, ↓reduceIte, ite_true, ite_false]
  simp (config := { maxSteps := 10000000, decide := true }) only [SimdShuf.interp,
    BitVec.ofLanes, BitVec.lane, List.range, List.range.loop, List.foldl,
    BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero, BitVec.reduceGetLsb,
    BitVec.reduceExtractLsb', BitVec.reduceAnd, BitVec.reduceToNat, BitVec.msb_eq_getLsbD_last,
    Nat.reduceLT, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.and_true,
    Bool.and_false, Bool.not_true, Bool.not_false, Bool.or_false, Bool.false_or, ite_true,
    ite_false, ↓reduceIte, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv,
    Nat.reduceMod, Bool.false_eq_true, and_true, true_and]

end AesCtrX86
