/-
Axiom audit: the theorems may depend only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). In particular no `sorry`
(`sorryAx`), no `bv_decide`/`native_decide` (`Lean.ofReduceBool`,
`Lean.trustCompiler`), and no axiom of our own.
-/
import AesCtr.Theorems

/-- info: 'AesCtr.ctrBlocksBulkAsm_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AesCtr.ctrBlocksBulkAsm_correct

/-- info: 'AesCtr.ctrBlocksBulkEOR3Asm_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AesCtr.ctrBlocksBulkEOR3Asm_correct

/-- info: 'AesCtr.ctrBlocks1Asm_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AesCtr.ctrBlocks1Asm_correct

/-- info: 'AesCtr.kat_fips197_c1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AesCtr.kat_fips197_c1

/-- info: 'AesCtr.kat_fips197_c2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AesCtr.kat_fips197_c2

/-- info: 'AesCtr.kat_fips197_c3' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AesCtr.kat_fips197_c3

/-- info: 'AesCtr.ctrBlocks2Asm_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AesCtr.ctrBlocks2Asm_correct

/-- info: 'AesCtr.ctrBlocks4Asm_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AesCtr.ctrBlocks4Asm_correct

/-- info: 'AesCtr.ctrBlocks8Asm_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AesCtr.ctrBlocks8Asm_correct
