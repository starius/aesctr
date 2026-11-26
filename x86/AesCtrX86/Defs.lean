/-
A call of one of the functions (`Call`), what it must leave in memory
(`Call.out`, `MemInv`), and the arithmetic of addresses.
-/
import AesCtrX86.Spec
import AesCtrX86.MemLib
import Kraken.X64.Semantics

open Std Std.ExtHashMap

namespace AesCtrX86

/-- Address of block `i` of the buffer at `base`. -/
def blockAddr (base : BitVec 64) (i : Nat) : BitVec 64 := base + BitVec.ofNat 64 (16 * i)

/-- The 16 bytes at `a` hold the block `x`. -/
def Holds (m : Mem 64) (a : BitVec 64) (x : BitVec 128) : Prop :=
  Mem.loadInt m a 16 = some (x.toNat : Int)

/-- One call of `ctrBlocksBulkAsm(nr, xk, dst, src, n, ivlo, ivhi, vaes)` and the
machine it starts on: the stack pointer, general-purpose registers and memory at
entry, the round keys and source blocks in that memory, and the return
address. -/
structure Call where
  nr : Nat
  xk : BitVec 64
  dst : BitVec 64
  src : BitVec 64
  n : Nat
  ivlo : BitVec 64
  ivhi : BitVec 64
  rsp : BitVec 64
  regs : Reg64s
  mem : Mem 64
  rk : Nat → BitVec 128
  srcb : Nat → BitVec 128
  ra : BitVec 64

/-- What block `i` of `dst` must hold when the call returns. -/
def Call.out (c : Call) (i : Nat) : BitVec 128 :=
  c.srcb i ^^^ keystream c.nr c.rk c.ivhi c.ivlo i

/-- After `b` blocks: `dst` blocks `0 .. b-1` hold their output, and every
other byte is as at entry. -/
structure MemInv (c : Call) (b : Nat) (m : Mem 64) : Prop where
  done : ∀ i < b, Holds m (blockAddr c.dst i) (c.out i)
  frame : ∀ a, ¬ InR a c.dst (16 * b) → m[a]? = c.mem[a]?

/-! ## Addresses as natural numbers

All ranges in a call fit below 2^64, so the questions of overlap are about
intervals of natural numbers. -/

theorem toNat_add_of_lt (x : BitVec 64) (k : Nat) (h : x.toNat + k < 2 ^ 64) :
    (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  exact Nat.mod_eq_of_lt h

theorem inR_iff (k a : BitVec 64) (n : Nat) (h : a.toNat + n ≤ 2 ^ 64) :
    InR k a n ↔ a.toNat ≤ k.toNat ∧ k.toNat < a.toNat + n := by
  unfold InR
  rw [BitVec.toNat_sub]
  have ha := a.isLt
  have hk := k.isLt
  constructor
  · intro h1
    by_cases hka : a.toNat ≤ k.toNat
    · rw [show 2 ^ 64 - a.toNat + k.toNat = 2 ^ 64 + (k.toNat - a.toNat) by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at h1
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at h1
      omega
  · intro ⟨h1, h2⟩
    rw [show 2 ^ 64 - a.toNat + k.toNat = 2 ^ 64 + (k.toNat - a.toNat) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    omega

theorem blockAddr_toNat (base : BitVec 64) (i : Nat) (h : base.toNat + 16 * i < 2 ^ 64) :
    (blockAddr base i).toNat = base.toNat + 16 * i :=
  toNat_add_of_lt base (16 * i) h

/-- Moving `c` bytes past block `i` (with `c` a multiple of 16) is block `i + c/16`. -/
theorem blockAddr_add (base : BitVec 64) (i c : Nat) (hc : c % 16 = 0) :
    blockAddr base i + BitVec.ofNat 64 c = blockAddr base (i + c / 16) := by
  unfold blockAddr
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  omega

theorem blockAddr_zero (base : BitVec 64) : blockAddr base 0 = base := by
  simp [blockAddr]

/-- An immediate operand, as a bit vector. -/
theorem toBitVec_lit (n : Nat) : Int64.toBitVec (no_index (OfNat.ofNat n)) = BitVec.ofNat 64 n := rfl

/-! `add $k, %r` computes `k + r`: these put the result back in normal form. -/

theorem ofNat_add_blockAddr (base : BitVec 64) (i k : Nat) (hk : k % 16 = 0) :
    BitVec.ofNat 64 k + blockAddr base i = blockAddr base (i + k / 16) := by
  rw [BitVec.add_comm, blockAddr_add _ _ _ hk]

theorem ofNat_add_xk (c : Call) (k : Nat) :
    BitVec.ofNat 64 k + c.xk = c.xk + BitVec.ofNat 64 k := BitVec.add_comm _ _

theorem ofNat_add_add (x : BitVec 64) (j k : Nat) :
    BitVec.ofNat 64 k + (x + BitVec.ofNat 64 j) = x + BitVec.ofNat 64 (j + k) := by
  rw [BitVec.add_comm, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Constant offsets add up. -/
theorem add_ofNat_ofNat (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

end AesCtrX86
