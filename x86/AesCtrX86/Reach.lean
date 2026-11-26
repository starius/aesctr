/-
Composing runs of a program block by block.

Kraken's `straightlineStep e st P` runs `e` from `st` until a taken jump, and
`Eventually (straightlineStep e) Q st` says that every run from `st` reaches a
state satisfying `Q`. A label does not stop a straight-line run, so the proofs
use `Runs e Q st`: running from `st` (wherever it started), every run reaches
`Q`. When the code before a label falls through into it, what is left to show
is exactly `Runs e Q` at the label, so a proof can be split at any label.
-/
import Kraken.OmniSemantics
import Kraken.X64.OmniSemantics

namespace AesCtrX86

/-- Every run of `e` from `st` eventually reaches a state satisfying `Q`. -/
abbrev Reaches [Layout] (e : Executable) (Q : MachineState → Prop) (st : MachineState) : Prop :=
  Eventually (straightlineStep e) Q st

/-- Running `e` from `st`, every run eventually reaches a state satisfying `Q`. -/
def Runs [Layout] (e : Executable) (Q : MachineState → Prop) (st : MachineState) : Prop :=
  straightlineStep e st (Reaches e Q)

theorem Effects.All_mono {P P' : MachineState → Prop} (h : ∀ st, P st → P' st) :
    ∀ e : Effects, e.All P → e.All P'
  | .done a, hp => h a hp
  | .unimplemented _, hp => hp
  | .gp_unaligned .., hp => hp
  | .fault _, hp => hp
  | .nonmem_load .., hp => hp
  | .nonmem_store .., hp => hp
  | @Effects.undefined _ _ cont, hp => fun v => Effects.All_mono h (cont v) (hp v)
  | .require_read_access _ _ ok, hp => Effects.All_mono h (ok ()) hp
  | .require_write_access _ _ ok, hp => Effects.All_mono h (ok ()) hp
  | .require_exec_access _ ok, hp => Effects.All_mono h (ok ()) hp

variable [Layout]

theorem reaches_of_runs {e : Executable} {Q : MachineState → Prop} {st : MachineState}
    (h : Runs e Q st) : Reaches e Q st :=
  step_cps _ _ _ h

/-- What `Runs` unfolds to: the directives from the current address, run with the
final continuation. -/
theorem runs_def (e : Executable) (Q : MachineState → Prop) (s : MachineData) (pc : Int64) :
    Runs e Q (s, pc) =
      Effects.All (Reaches e Q)
        (@Directives.interp (Executable.labels e) (e.directivesFromAddress pc) s pc
          (fun pc s => .done (s, pc))) := rfl

theorem reaches_done {e : Executable} {Q : MachineState → Prop} {st : MachineState}
    (h : Q st) : Reaches e Q st :=
  .done st h

end AesCtrX86
