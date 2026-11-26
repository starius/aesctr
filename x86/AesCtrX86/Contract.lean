/-
What the callers of the functions guarantee about the buffers (`Bufs`) and,
for `ctrBlocksBulkAsm`, about the call (`Pre`); and the facts about memory part
way through a call that follow from them.
-/
import AesCtrX86.Defs

open Std Std.ExtHashMap

namespace AesCtrX86

/-- `bswapMask` and `ctrOffsets` at their addresses in the linked binary. -/
def maskAddr : BitVec 64 := 0x55c890#64
def maskVal : BitVec 128 := 0x000102030405060708090a0b0c0d0e0f#128
def offAddr (k : Nat) : BitVec 64 := 0x55c940#64 + BitVec.ofNat 64 (16 * k)

/-- What every function needs of its buffers, for a call that encrypts `n`
blocks:
- `nr` is 10, 12 or 14 and `n ≥ 1`;
- the round keys, the `n` source blocks, the `n` destination blocks and the
  byte-reversal mask are in memory, and no buffer wraps around the address
  space;
- `dst` does not overlap the key schedule or the mask, and `src` is `dst` or
  does not overlap it. -/
structure Bufs (c : Call) : Prop where
  nr : c.nr = 10 ∨ c.nr = 12 ∨ c.nr = 14
  n_pos : 0 < c.n
  src_fit : c.src.toNat + 16 * c.n ≤ 2 ^ 64
  dst_fit : c.dst.toNat + 16 * c.n ≤ 2 ^ 64
  xk_fit : c.xk.toNat + 240 ≤ 2 ^ 64
  keys : ∀ i ≤ c.nr, Holds c.mem (blockAddr c.xk i) (c.rk i)
  srcs : ∀ i < c.n, Holds c.mem (blockAddr c.src i) (c.srcb i)
  dsts : ∀ i < c.n, ∃ z, Mem.loadInt c.mem (blockAddr c.dst i) 16 = some z
  mask : Holds c.mem maskAddr maskVal
  sep_keys : ∀ a, InR a c.dst (16 * c.n) → ¬ InR a c.xk 240
  sep_mask : ∀ a, InR a c.dst (16 * c.n) → ¬ InR a maskAddr 16
  src_dst : c.src = c.dst ∨ ∀ a, InR a c.dst (16 * c.n) → ¬ InR a c.src (16 * c.n)

/-- What the Go caller guarantees for `ctrBlocksBulkAsm(nr, xk, dst, src, n,
ivlo, ivhi, vaes)`, called with the stack pointer `c.rsp` and memory `c.mem`:
`Bufs`; the arguments are on the stack above the return address (Go ABI0);
the low 64 bits of the counter do not wrap within the `n` blocks; the table
`ctrOffsets` is in memory; and `dst` does not overlap the arguments or
`ctrOffsets`. -/
structure Pre (c : Call) (vaes : Bool) extends Bufs c : Prop where
  ctr : c.ivlo.toNat + c.n ≤ 2 ^ 64
  rsp_fit : c.rsp.toNat + 72 ≤ 2 ^ 64
  offs : ∀ k ≤ 16, Holds c.mem (offAddr k) (BitVec.ofNat 128 k)
  ret : Mem.loadInt c.mem c.rsp 8 = some (c.ra.toNat : Int)
  arg_nr : Mem.loadInt c.mem (c.rsp + 8#64) 8 = some (c.nr : Int)
  arg_xk : Mem.loadInt c.mem (c.rsp + 16#64) 8 = some (c.xk.toNat : Int)
  arg_dst : Mem.loadInt c.mem (c.rsp + 24#64) 8 = some (c.dst.toNat : Int)
  arg_src : Mem.loadInt c.mem (c.rsp + 32#64) 8 = some (c.src.toNat : Int)
  arg_n : Mem.loadInt c.mem (c.rsp + 40#64) 8 = some (c.n : Int)
  arg_ivlo : Mem.loadInt c.mem (c.rsp + 48#64) 8 = some (c.ivlo.toNat : Int)
  arg_ivhi : Mem.loadInt c.mem (c.rsp + 56#64) 8 = some (c.ivhi.toNat : Int)
  arg_vaes : Mem.loadInt c.mem (c.rsp + 64#64) 1 = some (if vaes then 1 else 0)
  sep_stack : ∀ a, InR a c.dst (16 * c.n) → ¬ InR a c.rsp 72
  sep_offs : ∀ a, InR a c.dst (16 * c.n) → ¬ InR a (offAddr 0) 272

/-! ## Loads from memory part way through the call

`MemInv c b m` changes only the first `b` blocks of `dst`; so the keys, the
constants, the stack, the source blocks from `b` on and the destination blocks
from `b` on read as at entry. -/

/-- A 16-byte load that misses the first `b` blocks of `dst` reads as at entry. -/
theorem loadInt_frame {c : Call} {b : Nat} {m : Mem 64} (hinv : MemInv c b m) (a : BitVec 64)
    (k : Nat) (h : ∀ i < k, ¬ InR (a + BitVec.ofNat 64 i) c.dst (16 * b)) :
    Mem.loadInt m a k = Mem.loadInt c.mem a k :=
  loadInt_congr m c.mem a k (fun i hi => hinv.frame _ (h i hi))

/-- The stores of a group: `(i, v)` stores `v` into block `i` of `base`, in order. -/
def stores (m : Mem 64) (base : BitVec 64) : List (Nat × Int) → Mem 64
  | [] => m
  | (i, v) :: l => stores (Mem.storeInt m (blockAddr base i) 16 v) base l

theorem loadInt_stores (m : Mem 64) (base : BitVec 64) (l : List (Nat × Int)) (a : BitVec 64)
    (k : Nat) (h : ∀ p ∈ l, ∀ i < k, ¬ InR (a + BitVec.ofNat 64 i) (blockAddr base p.1) 16) :
    Mem.loadInt (stores m base l) a k = Mem.loadInt m a k := by
  induction l generalizing m with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨i, v⟩ := p
    simp only [stores]
    rw [ih _ (fun q hq => h q (List.mem_cons_of_mem _ hq)),
      loadInt_storeInt_other _ _ _ _ _ _ (by decide) (h (i, v) (List.mem_cons_self ..))]

end AesCtrX86

namespace AesCtrX86

/-! ## Byte arithmetic -/

theorem inR_mono {k a : BitVec 64} {n n' : Nat} (h : InR k a n) (hn : n ≤ n') : InR k a n' := by
  unfold InR at *; omega

theorem toNat_add_ofNat (x : BitVec 64) (t : Nat) (h : x.toNat + t < 2 ^ 64) :
    (x + BitVec.ofNat 64 t).toNat = x.toNat + t := toNat_add_of_lt x t h

/-- Byte `t` of block `i` of a buffer that fits below 2^64. -/
theorem blockByte_toNat (base : BitVec 64) (i t : Nat) (ht : t < 16)
    (h : base.toNat + 16 * (i + 1) ≤ 2 ^ 64) :
    (blockAddr base i + BitVec.ofNat 64 t).toNat = base.toNat + 16 * i + t := by
  rw [toNat_add_ofNat _ _ (by rw [blockAddr_toNat _ _ (by omega)]; omega),
    blockAddr_toNat _ _ (by omega)]

/-- Byte `t` of block `i` is in the first `16 * b` bytes iff `i < b`. -/
theorem inR_blockByte (base : BitVec 64) (i t b : Nat) (ht : t < 16)
    (hi : base.toNat + 16 * (i + 1) ≤ 2 ^ 64) (hb : base.toNat + 16 * b ≤ 2 ^ 64) :
    InR (blockAddr base i + BitVec.ofNat 64 t) base (16 * b) ↔ i < b := by
  rw [inR_iff _ _ _ hb, blockByte_toNat _ _ _ ht hi]
  omega

/-- Byte `t` of block `i` is in block `j` iff `i = j`. -/
theorem inR_blockByte_block (base : BitVec 64) (i j t : Nat) (ht : t < 16)
    (hi : base.toNat + 16 * (i + 1) ≤ 2 ^ 64) (hj : base.toNat + 16 * (j + 1) ≤ 2 ^ 64) :
    InR (blockAddr base i + BitVec.ofNat 64 t) (blockAddr base j) 16 ↔ i = j := by
  rw [inR_iff _ _ _ (by rw [blockAddr_toNat _ _ (by omega)]; omega),
    blockByte_toNat _ _ _ ht hi, blockAddr_toNat _ _ (by omega)]
  omega

/-! ## The state of the call -/

/-- Writing the output of block `b` extends the memory invariant to `b + 1`. -/
theorem memInv_store {c : Call} (hc : Bufs c) {b : Nat} {m : Mem 64}
    (hinv : MemInv c b m) (hb : b < c.n) (x : BitVec 128) (hx : x = c.out b) :
    MemInv c (b + 1) (Mem.storeInt m (blockAddr c.dst b) 16 x.toInt) := by
  have hfit := hc.dst_fit
  constructor
  · intro i hi
    unfold Holds
    by_cases hib : i = b
    · subst hib; rw [loadInt_store128_self, hx]
    · rw [loadInt_storeInt_other _ _ _ _ _ _ (by decide) (fun t ht hin => hib
        ((inR_blockByte_block c.dst i b t ht (by omega) (by omega)).mp hin))]
      exact hinv.done i (by omega)
  · intro a ha
    rw [getElem?_storeInt_of_not _ _ _ _ _ (by decide)]
    · exact hinv.frame a (fun h => ha (inR_mono h (by omega)))
    · intro hin
      apply ha
      rw [inR_iff _ _ _ (by omega)]
      rw [inR_iff _ _ _ (by rw [blockAddr_toNat _ _ (by omega)]; omega),
        blockAddr_toNat _ _ (by omega)] at hin
      omega

end AesCtrX86
