/-
`xstep`: one `simp` pass over Kraken's x86 semantics (the instruction
definitions, address and register normal forms, literal arithmetic) with the
facts of the current segment.
-/
import AesCtrX86.Blocks
import AesCtrX86.Steps
import AesCtrX86.Final
import AesCtrX86.Defs
import AesCtrX86.Flags
import AesCtrX86.Values
import Kraken.SeparationMem

open Std Std.ExtHashMap

namespace AesCtrX86

-- One `simp` pass over Kraken's semantics, with extra facts `hs`.
open Lean.Parser.Tactic in
syntax "xstep" " [" simpLemma,* "]" : tactic
macro_rules
  | `(tactic| xstep [$hs,*]) => `(tactic|
    simp (config := { maxSteps := 10000000, decide := true }) only [
      Directives.interp, Directive.interp, Instr.interp, Operation.interp, AvxOperation.interp,
      Effects.All, MachineData.load, MachineData.loadAvx, MachineData.store,
      MachineData.storeAvx, require_access_chunks, Operand.interp, RegOrMem.interp,
      AvxRegOrMem.interp, AvxRegOrMem.interpSimd, AddrExpr.interp, ConstExpr.interp,
      ConstExpr.imm8, Option.imm8, BitVec.toAddressSize, Reg64s.get64, Reg64s.get, Reg64s.set,
      Reg64s.set64, Reg.base, Reg.offset, Width.bits, Width.bytes, AvxWidth.bits,
      AvxWidth.bytes, MachineData.set, MachineData.setReg, MachineData.setAvxReg,
      MachineData.setAvx, RegZmms.get, RegZmms.get512, RegZmms.set, RegZmms.set512,
      RegZmms.setLegacy, AvxReg.base, SimdInsertOp.interp, SimdInsertOp.memBits,
      SimdBinOp.eval, SimdBinOp.interp, SimdBinOp.swappedInterp?, SimdMov.aligned,
      SimdLogic.interp, Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true,
      StatusFlags.from_result, CondCode.interp, subFlags_fst, addFlags_fst, subFlags_cf, subFlags_zf,
      blockAddr_add, add_ofNat_ofNat, paddq_ctr, BitVec.ofNat_toNat, toBitVec_lit, ofNat_add_blockAddr, ofNat_add_xk,
      ofNat_add_add, BitVec.add_zero, BitVec.sub_zero,
      SimdBinOp.memBytes?, take_eq, take_eq_zmm, setWidth_replaceLow, setWidth_replaceLow_zmm, replaceLow_replaceLow_zmm, addr_reg, addr_reg', addr_reg0, ofInt_toNat, ofInt_toNat128,
      drop_zero, map2_128, start,
      Int64.reduceToInt, BitVec.ofInt_ofNat, Int64.reduceAdd, Int64.reduceOfNat,
      List.zip, List.zipWith, List.cons_append, List.nil_append,
      BitVec.zeroExtend_eq_setWidth, BitVec.truncate_eq_setWidth, BitVec.setWidth_eq,
      ite_true, ite_false, ↓reduceIte, Int.reduceAdd, Int.add_zero, 
      BitVec.reduceAnd, BitVec.reduceOr, BitVec.reduceXOr, BitVec.reduceAdd, BitVec.reduceSub,
      BitVec.reduceExtractLsb', BitVec.reduceSetWidth, BitVec.reduceOfInt, BitVec.reduceULT,
      BitVec.reduceEq, BitVec.reduceBEq, BitVec.reduceGetMsb, BitVec.reduceCpop, BitVec.reduceAppend,
      BitVec.reduceShiftLeft, BitVec.reduceHShiftLeft, BitVec.reduceHShiftRight, BitVec.reduceToNat,
      Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, Nat.reduceDiv, Nat.add_assoc, Bool.false_eq_true, $hs,*])

end AesCtrX86
