/-
Axiom audit, checked by `#guard_msgs`: the check fails if a theorem's axioms
change. The theorems depend only on Lean's three standard axioms: there is no
`sorry`, and no `native_decide` or `bv_decide` (which would add
`Lean.ofReduceBool` and the axioms of their compiled checks).
-/
import AesCtrX86

/-- info: 'AesCtrX86.ctrBlocksBulkAsm_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AesCtrX86.ctrBlocksBulkAsm_correct

/-- info: 'AesCtrX86.ctrBlocks1Asm_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AesCtrX86.ctrBlocks1Asm_correct

/-- info: 'AesCtrX86.ctrBlocks2Asm_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AesCtrX86.ctrBlocks2Asm_correct

/-- info: 'AesCtrX86.ctrBlocks4Asm_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AesCtrX86.ctrBlocks4Asm_correct

/-- info: 'AesCtrX86.ctrBlocks8Asm_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AesCtrX86.ctrBlocks8Asm_correct

/-- info: 'AesCtrX86.layout_prog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AesCtrX86.layout_prog

/-- info: 'AesCtrX86.kat_fips197_c1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AesCtrX86.kat_fips197_c1

/-- info: 'AesCtrX86.kat_fips197_c2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AesCtrX86.kat_fips197_c2

/-- info: 'AesCtrX86.kat_fips197_c3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AesCtrX86.kat_fips197_c3
