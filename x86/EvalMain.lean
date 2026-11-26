import AesCtrX86.Run

open AesCtrX86

def main : IO UInt32 := do
  let mut passed := 0
  let mut failed := 0
  for c in cases do
    match runCase c with
    | .ok true => passed := passed + 1
    | .ok false =>
      failed := failed + 1
      IO.println s!"FAIL {c.describe}"
    | .error e =>
      failed := failed + 1
      IO.println s!"ERROR {c.describe}: {e}"
  IO.println s!"{passed} passed, {failed} failed"
  return if failed == 0 then 0 else 1
