/-
Helpers for proving fixed-width `BitVec` identities bit by bit with `simp`, so
that the proofs use only Lean's standard axioms (no `bv_decide`).

The method: `ext128` turns `x = y` into one equation per bit, `List.range`
enumerates the 128 bit indices, and `simp` evaluates each bit of both sides
with the `getLsbD` lemmas of each operation.

Two pitfalls shape the proofs that use these helpers:
- `simp` cannot use `BitVec.getLsbD_append` where the width of `getLsbD` is a
  literal (`128`) but the concatenation has a sum type (`64 + 64`): the
  `getLsbD_append_*` lemmas below state it at the literal widths that occur.
- `Nat.reduceAdd` also folds the sums in the implicit widths of `getLsbD`
  (`8 + 8 + 8` becomes `24`), after which the general lemma no longer matches,
  so the proofs remove concatenations before they reduce index arithmetic.
-/

namespace AesCtrX86

open BitVec

/-- Two 128-bit values are equal if all their bits are. -/
theorem ext128 {x y : BitVec 128} (h : ∀ i ∈ List.range 128, x.getLsbD i = y.getLsbD i) :
    x = y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact h i (List.mem_range.mpr hi)

theorem forall_mem_nil' {p : Nat → Prop} : (∀ i ∈ ([] : List Nat), p i) ↔ True := by simp

/-- `getLsbD_append` at width 128 for `[hi, lo]` 64-bit halves. -/
theorem getLsbD_append_64_64 (x y : BitVec 64) (i : Nat) :
    @BitVec.getLsbD 128 (x ++ y) i = if i < 64 then y.getLsbD i else x.getLsbD (i - 64) :=
  BitVec.getLsbD_append

/-- `getLsbD_append` at width 64 for eight bytes (`bswap64`). -/
theorem getLsbD_append_bswap (x : BitVec (8 + 8 + 8 + 8 + 8 + 8 + 8)) (y : BitVec 8) (i : Nat) :
    @BitVec.getLsbD 64 (x ++ y) i = if i < 8 then y.getLsbD i else x.getLsbD (i - 8) :=
  BitVec.getLsbD_append

/-- `getLsbD_append` at width 128 for sixteen bytes (LNSym's `ShiftRows` and
`MixColumns`). -/
theorem getLsbD_append_top128 (x : BitVec (8+8+8+8+8+8+8+8+8+8+8+8+8+8+8)) (y : BitVec 8)
    (i : Nat) :
    @BitVec.getLsbD 128 (x ++ y) i = if i < 8 then y.getLsbD i else x.getLsbD (i - 8) :=
  BitVec.getLsbD_append

/-- `getLsbD_append` at width 32 for four bytes (the columns of LNSym's
`MixColumns`). -/
theorem getLsbD_append_top32 (x : BitVec (8+8+8)) (y : BitVec 8) (i : Nat) :
    @BitVec.getLsbD 32 (x ++ y) i = if i < 8 then y.getLsbD i else x.getLsbD (i - 8) :=
  BitVec.getLsbD_append

theorem getLsbD_ite' {w : Nat} (c : Prop) [Decidable c] (a b : BitVec w) (i : Nat) :
    (if c then a else b).getLsbD i = if c then a.getLsbD i else b.getLsbD i := by
  split <;> rfl

theorem ite_true_false_bool (b : Bool) : (if b = true then true else false) = b := by
  cases b <;> rfl

theorem getLsbD_ge8 (x : BitVec 8) (i : Nat) (h : 8 ≤ i) : x.getLsbD i = false :=
  BitVec.getLsbD_of_ge x i h

end AesCtrX86
