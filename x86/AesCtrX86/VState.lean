/-
The state of the VAES path between groups of blocks.
-/
import AesCtrX86.NIState
import AesCtrX86.VLemmas
import AesCtrX86.Tactic
import AesCtrX86.Reach

open Std Std.ExtHashMap

namespace AesCtrX86

/-- The registers and memory of the VAES path after `b` blocks: as on the
AES-NI path, except that Y9 holds the counter `[ivlo + b, ivhi]` in both lanes
and Y10 the byte-reversal mask in both lanes. -/
structure VRegs (c : Call) (b : Nat) (s : MachineData) : Prop where
  rax : s.regs.rax.toBitVec = BitVec.ofNat 64 c.nr
  rbx : s.regs.rbx.toBitVec = c.xk
  rsi : s.regs.rsi.toBitVec = blockAddr c.src b
  rdx : s.regs.rdx.toBitVec = blockAddr c.dst b
  rsp : s.regs.rsp = c.regs.rsp
  rbp : s.regs.rbp = c.regs.rbp
  r14 : s.regs.r14 = c.regs.r14
  r15 : s.regs.r15 = c.regs.r15
  y9 : BitVec.setWidth 256 s.zmms.zmm9 =
    (c.ivhi ++ (c.ivlo + BitVec.ofNat 64 b)) ++ (c.ivhi ++ (c.ivlo + BitVec.ofNat 64 b))
  y10 : BitVec.setWidth 256 s.zmms.zmm10 =
    5233100606242806050955395731361295#128 ++ 5233100606242806050955395731361295#128
  mem : MemInv c b s.dmem

theorem VRegs.final {c : Call} {b : Nat} {s : MachineData} (h : VRegs c b s) :
    NIFinal c b s := ⟨h.rsp, h.rbp, h.r14, h.r15, h.mem⟩

/-- A `test` or `cmp` changes only the flags. -/
theorem vRegs_status {c : Call} {b : Nat} {s : MachineData} (h : VRegs c b s)
    (st : StatusFlags) : VRegs c b { s with status := st } :=
  ⟨h.rax, h.rbx, h.rsi, h.rdx, h.rsp, h.rbp, h.r14, h.r15, h.y9, h.y10, h.mem⟩

/-- The low lane of Y9, which the group of one block reads as X9. -/
theorem setWidth_128_of_256 (x : ZmmValue) (v : BitVec 256)
    (h : @BitVec.setWidth 512 256 x = v) : @BitVec.setWidth 512 128 x = BitVec.setWidth 128 v := by
  rw [← h]
  exact (BitVec.setWidth_setWidth_of_le (w := 512) x (by decide)).symm

theorem VRegs.x9 {c : Call} {b : Nat} {s : MachineData} (h : VRegs c b s) :
    BitVec.setWidth 128 s.zmms.zmm9 = c.ivhi ++ (c.ivlo + BitVec.ofNat 64 b) := by
  rw [setWidth_128_of_256 _ _ h.y9, setWidth_128_256]

theorem VRegs.x10 {c : Call} {b : Nat} {s : MachineData} (h : VRegs c b s) :
    BitVec.setWidth 128 s.zmms.zmm10 = 5233100606242806050955395731361295#128 := by
  rw [setWidth_128_of_256 _ _ h.y10, setWidth_128_256]

/-! The `test $k, %rdi` of the tail, with `r0 < 16` blocks left after the loop. -/

theorem vtest_bit_8 : ∀ r0, r0 < 16 →
    (BitVec.ofNat 64 r0 &&& BitVec.ofNat 64 8 == BitVec.zero 64) = !decide (8 ≤ r0 % 16) := by
  decide
theorem vtest_bit_4 : ∀ r0, r0 < 16 →
    (BitVec.ofNat 64 r0 &&& BitVec.ofNat 64 4 == BitVec.zero 64) = !decide (4 ≤ r0 % 8) := by
  decide
theorem vtest_bit_2 : ∀ r0, r0 < 16 →
    (BitVec.ofNat 64 r0 &&& BitVec.ofNat 64 2 == BitVec.zero 64) = !decide (2 ≤ r0 % 4) := by
  decide
theorem vtest_bit_1 : ∀ r0, r0 < 16 →
    (BitVec.ofNat 64 r0 &&& BitVec.ofNat 64 1 == BitVec.zero 64) = !decide (1 ≤ r0 % 2) := by
  decide

-- `xstep` with the lemmas for 256-bit values and 32-byte accesses.
open Lean.Parser.Tactic in
syntax "vstep" " [" simpLemma,* "]" : tactic
macro_rules
  | `(tactic| vstep [$hs,*]) => `(tactic|
    xstep [map2_256, lane1_append, lane0_append, lane0_setWidth, lane_lit, ofLanes_256, append_eq,
      setWidth_256_512, setWidth_128_512, setWidth_128_256, ofInt_toNat256, storeInt_32,
      SimdUnOp.interp, SimdUnOp.memBytes?, $hs,*])

end AesCtrX86
