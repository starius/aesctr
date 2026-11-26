/-
Master's fixed-size functions `ctrBlocks1Asm`, `ctrBlocks2Asm`, `ctrBlocks4Asm`
and `ctrBlocks8Asm`: what their caller guarantees, and the lemmas for their
counter. They keep the counter in two 64-bit registers and step it with
`ADDQ $1` on the low half and `ADCQ $0` on the high half, so it wraps modulo
2^128 as the spec says; `ctrBlocks8Asm` uses `PADDQ` instead when the low half
cannot wrap within the 8 blocks.
-/
import AesCtrX86.NIState
import AesCtrX86.Tactic
import AesCtrX86.Reach

open Std Std.ExtHashMap

namespace AesCtrX86

/-- What the Go caller guarantees for `ctrBlocks<n>Asm(nr, xk, dst, src, ivlo,
ivhi)`, with `n = c.n`, called with the stack pointer `c.rsp` and memory
`c.mem`: `Bufs`; the arguments are on the stack above the return address (Go
ABI0); and `dst` does not overlap the arguments. The counter may wrap. -/
structure PreF (c : Call) extends Bufs c : Prop where
  rsp_fit : c.rsp.toNat + 56 ≤ 2 ^ 64
  ret : Mem.loadInt c.mem c.rsp 8 = some (c.ra.toNat : Int)
  arg_nr : Mem.loadInt c.mem (c.rsp + 8#64) 8 = some (c.nr : Int)
  arg_xk : Mem.loadInt c.mem (c.rsp + 16#64) 8 = some (c.xk.toNat : Int)
  arg_dst : Mem.loadInt c.mem (c.rsp + 24#64) 8 = some (c.dst.toNat : Int)
  arg_src : Mem.loadInt c.mem (c.rsp + 32#64) 8 = some (c.src.toNat : Int)
  arg_ivlo : Mem.loadInt c.mem (c.rsp + 40#64) 8 = some (c.ivlo.toNat : Int)
  arg_ivhi : Mem.loadInt c.mem (c.rsp + 48#64) 8 = some (c.ivhi.toNat : Int)
  sep_stack : ∀ a, InR a c.dst (16 * c.n) → ¬ InR a c.rsp 56

/-! ## The counter in two registers -/

/-- The low and high 64 bits of a 128-bit counter. -/
def lo64 (t : BitVec 128) : BitVec 64 := t.setWidth 64
def hi64 (t : BitVec 128) : BitVec 64 := t.extractLsb' 64 64

theorem lo64_append (hi lo : BitVec 64) : lo64 (hi ++ lo) = lo :=
  BitVec.setWidth_append_eq_right

theorem hi64_append (hi lo : BitVec 64) : hi64 (hi ++ lo) = hi :=
  BitVec.extractLsb'_append_eq_left

theorem toNat_lo64 (t : BitVec 128) : (lo64 t).toNat = t.toNat % 2 ^ 64 := by
  simp [lo64, BitVec.toNat_setWidth]

theorem toNat_hi64 (t : BitVec 128) : (hi64 t).toNat = t.toNat / 2 ^ 64 := by
  have := t.isLt
  simp only [hi64, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- The two halves, back in one register (`MOVQ` and `PINSRQ $1`). -/
theorem hi64_append_lo64 (t : BitVec 128) : hi64 t ++ lo64 t = t := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (lo64 t).isLt, Nat.shiftLeft_eq,
    toNat_lo64, toNat_hi64]
  omega

/-- `ADDQ $1` on the low half. -/
theorem add_lo64 (t : BitVec 128) : BitVec.ofNat 64 1 + lo64 t = lo64 (t + BitVec.ofNat 128 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, toNat_lo64, BitVec.toNat_ofNat]
  omega

/-- `ADCQ $0` on the high half, with the carry of `ADDQ $1` on the low half. -/
theorem toNat_zero64 : BitVec.toNat (0 : BitVec 64) = 0 := rfl
theorem toNat_one64 : BitVec.toNat (1 : BitVec 64) = 1 := rfl

theorem adc_hi64 (st st' : StatusFlags) (t : BitVec 128) :
    (addFlags st' (BitVec.ofNat 64 0) (hi64 t)
      (addFlags st (BitVec.ofNat 64 1) (lo64 t)).snd.cf).fst = hi64 (t + BitVec.ofNat 128 1) := by
  have ht := t.isLt
  have hcf : (addFlags st (BitVec.ofNat 64 1) (lo64 t)).snd.cf =
      decide (t.toNat % 2 ^ 64 = 2 ^ 64 - 1) := by
    simp only [addFlags, StatusFlags.from_result, BitVec.unsigned, Bool.false_eq_true,
      ↓reduceIte, BitVec.add_zero, Int.add_zero]
    rw [Bool.eq_iff_iff, bne_iff_ne, ne_eq, decide_eq_true_iff]
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, toNat_lo64, toNat_zero64]
    omega
  rw [hcf]
  apply BitVec.eq_of_toNat_eq
  by_cases h : t.toNat % 2 ^ 64 = 2 ^ 64 - 1
  · simp only [addFlags, h, decide_true, ↓reduceIte, BitVec.toNat_add, BitVec.toNat_ofNat,
      toNat_hi64, toNat_one64]
    omega
  · simp only [addFlags, h, decide_false, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_add,
      BitVec.toNat_ofNat, toNat_hi64, toNat_zero64]
    omega

/-- Steps of the 128-bit counter add up. -/
theorem add_ofNat_ofNat128 (x : BitVec 128) (a b : Nat) :
    x + BitVec.ofNat 128 a + BitVec.ofNat 128 b = x + BitVec.ofNat 128 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- The carry of `ADDQ $k` (`ctrBlocks8Asm` checks whether the low half of the
counter wraps within its 8 blocks). -/
theorem addFlags_cf (st : StatusFlags) (k : Nat) (x : BitVec 64) (hk : k < 2 ^ 64) :
    (addFlags st (BitVec.ofNat 64 k) x).snd.cf = decide (2 ^ 64 ≤ k + x.toNat) := by
  have hx := x.isLt
  simp only [addFlags, StatusFlags.from_result, BitVec.unsigned, Bool.false_eq_true,
    ↓reduceIte, BitVec.add_zero, Int.add_zero]
  rw [Bool.eq_iff_iff, bne_iff_ne, ne_eq, decide_eq_true_iff]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, toNat_zero64]
  omega

/-- The carry of `ADDQ $7`, for 7 only, so that `simp` leaves the carry of
`ADDQ $1` to `adc_hi64`. -/
theorem addFlags_cf7 (st : StatusFlags) (x : BitVec 64) :
    (addFlags st (BitVec.ofNat 64 7) x).snd.cf = decide (18446744073709551616 ≤ 7 + x.toNat) :=
  addFlags_cf st 7 x (by decide)

theorem ofLanes_128_64 (f : Nat → BitVec 64) : BitVec.ofLanes 128 64 f = f 1 ++ f 0 := by
  have hr : List.range 2 = [0, 1] := by decide
  simp only [BitVec.ofLanes, Nat.reduceDiv, hr, List.foldl_cons, List.foldl_nil, Nat.zero_mul,
    Nat.one_mul, BitVec.shiftLeft_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append]
  by_cases h : i < 64
  · simp [h, hi]
  · have h2 : (f 0).getLsbD i = false := BitVec.getLsbD_of_ge _ _ (by omega)
    have h3 : i - 64 < 128 := by omega
    simp [h, hi, h2, h3]

/-- `PINSRQ $0` of `x` into a zeroed register (`ctrBlocks8Asm`'s step of 1). -/
theorem pinsrq_lo (x : BitVec 64) :
    (BitVec.ofLanes 128 64 fun i =>
      if (i == 0) = true then x else BitVec.lane 64 i (0#128 : BitVec 128)) = 0#64 ++ x := by
  rw [ofLanes_128_64]
  simp [BitVec.lane]

/-- The target of `JMP`, as the address literal of the block lemmas. -/
theorem ofBitVec_ofNat64 (n : Nat) : Int64.ofBitVec (BitVec.ofNat 64 n) = OfNat.ofNat n := rfl

theorem incFlags_fst {w : Nat} (st : StatusFlags) (a : BitVec w) : (incFlags st a).fst = a + 1 := by
  simp [incFlags]

/-! ## What the functions store -/

/-- What the fixed-size functions store for block `j`: the source block XOR the
encryption of the counter block `X`, which is `counter + j`. -/
theorem out_std (c : Call) (j : Nat) (X : BitVec 128)
    (hX : X = (c.ivhi ++ c.ivlo) + BitVec.ofNat 128 j) :
    c.srcb j ^^^ SimdCrypto.aesenclast.interp
      (encRounds c.rk (SimdShuf.pshufb.interp X 5233100606242806050955395731361295#128 ^^^
        c.rk 0) (c.nr - 1)) (c.rk c.nr) = c.out j := by
  subst hX
  rw [pshufb_bswap, encRounds_eq, aesenclast_eq]
  simp only [Call.out, keystream, aesEncrypt]

/-- The same, for the counter blocks of `PADDQ`, when the low half of the
counter does not wrap. -/
theorem out_fast (c : Call) (j : Nat) (hj : c.ivlo.toNat + j < 2 ^ 64) :
    c.srcb j ^^^ SimdCrypto.aesenclast.interp
      (encRounds c.rk (SimdShuf.pshufb.interp (c.ivhi ++ (c.ivlo + BitVec.ofNat 64 j))
        5233100606242806050955395731361295#128 ^^^ c.rk 0) (c.nr - 1)) (c.rk c.nr) = c.out j :=
  out_std c j _ (ctr_add _ _ _ hj)

/-! ## Facts for the runs -/

/-- The return address, after the stores into `dst`. -/
theorem ra_fact {c : Call} (hc : PreF c) (l : List (Nat × Int)) (hl : ∀ p ∈ l, p.1 < c.n) :
    Mem.loadInt (stores c.mem c.dst l) c.rsp 8 = some (c.ra.toNat : Int) := by
  have hfit := hc.rsp_fit
  rw [loadInt_stores _ _ _ _ _ (fun p hp t ht hin => hc.sep_stack _
    (inR_dst_of_block hc.toBufs (hl p hp) hin) (by
      unfold InR
      rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega))]
  exact hc.ret

theorem arg_src0 {c : Call} (hc : PreF c) :
    Mem.loadInt c.mem (c.rsp + 32#64) 8 = some ((blockAddr c.src 0).toNat : Int) := by
  rw [blockAddr_zero]; exact hc.arg_src

theorem arg_dst0 {c : Call} (hc : PreF c) :
    Mem.loadInt c.mem (c.rsp + 24#64) 8 = some ((blockAddr c.dst 0).toNat : Int) := by
  rw [blockAddr_zero]; exact hc.arg_dst

theorem arg_lo {c : Call} (hc : PreF c) :
    Mem.loadInt c.mem (c.rsp + 40#64) 8 = some ((lo64 (c.ivhi ++ c.ivlo)).toNat : Int) := by
  rw [lo64_append]; exact hc.arg_ivlo

theorem arg_hi {c : Call} (hc : PreF c) :
    Mem.loadInt c.mem (c.rsp + 48#64) 8 = some ((hi64 (c.ivhi ++ c.ivlo)).toNat : Int) := by
  rw [hi64_append]; exact hc.arg_ivhi

end AesCtrX86
