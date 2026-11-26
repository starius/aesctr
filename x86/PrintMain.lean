import AesCtrX86.Layout
import Kraken.X64.PrintATT

open AesCtrX86 in
/-- Prints function `<f>` as Kraken parsed it (`AesCtrX86.code_<f>`), with
Kraken's AT&T printer. Usage: `aesctr_print ctr1|ctr2|ctr4|ctr8|bulk`. -/
def main (args : List String) : IO UInt32 := do
  let code? : Option Program := match args with
    | ["ctr1"] => some code_ctr1
    | ["ctr2"] => some code_ctr2
    | ["ctr4"] => some code_ctr4
    | ["ctr8"] => some code_ctr8
    | ["bulk"] => some code_bulk
    | _ => none
  match code? with
  | some code =>
    IO.println (Kraken.X64.toATT code)
    return 0
  | none =>
    IO.eprintln "usage: aesctr_print ctr1|ctr2|ctr4|ctr8|bulk"
    return 2
