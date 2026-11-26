/-
`Executable.withAddresses` by structural recursion, which the kernel can
evaluate (Kraken's own definition is by well-founded recursion).
-/
import AesCtrX86.Layout

namespace AesCtrX86

/-- `Executable.withAddresses` by structural recursion, which the kernel can evaluate. -/
def withAddrs : Int64 → List (Directive × Nat) → List (Int64 × Directive × Nat)
  | _, [] => []
  | a, (d, n) :: ds => (a, d, n) :: withAddrs (a + .ofNat n) ds

theorem withAddresses_eq (a : Int64) (ds : List (Directive × Nat)) :
    Kraken.Executable.withAddresses (a, ds) = withAddrs a ds := by
  induction ds generalizing a with
  | nil => rw [Kraken.Executable.withAddresses]; rfl
  | cons d ds ih => rw [Kraken.Executable.withAddresses]; simp [withAddrs, ih]

end AesCtrX86
