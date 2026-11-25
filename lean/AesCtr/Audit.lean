/-
Axiom audit: the theorems may depend only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). In particular no `sorry`
(`sorryAx`), no `bv_decide`/`native_decide` (`Lean.ofReduceBool`,
`Lean.trustCompiler`), and no axiom of our own.
-/
import AesCtr.Theorems
import AesCtr.Proof.CtrBlocks2
import AesCtr.Proof.CtrBlocks4
import AesCtr.Proof.CtrBlocks8

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

-- The fixed-size functions the arm64 build no longer calls (still in the
-- assembly, unchanged from master).

/-- info: 'AesCtr.Base.ctrBlocks2_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AesCtr.Base.ctrBlocks2_correct

/-- info: 'AesCtr.Base.ctrBlocks4_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AesCtr.Base.ctrBlocks4_correct

/-- info: 'AesCtr.Base.ctrBlocks8_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AesCtr.Base.ctrBlocks8_correct
