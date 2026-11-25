/-
What is proved, in one place.

On arm64, crypto/internal/fips140/aes runs these assembly functions for CTR:
`ctrBlocksBulkAsm` or `ctrBlocksBulkEOR3Asm` (with FEAT_SHA3) for all full
blocks, and `ctrBlocks1Asm` for a partial block. If the low 64 bits of the
counter would wrap within the full blocks, it uses master's `ctrBlocks8Asm`,
`ctrBlocks4Asm`, `ctrBlocks2Asm` and `ctrBlocks1Asm` for them instead, as
before. Each theorem below is about the exact instruction words the Go
toolchain emits for that function (see `Bulk/Plain.lean`, `Bulk/Eor3.lean`,
`Final/CtrBlocks1.lean` and `Base/`, generated from the linked test binaries,
with the SHA-256 of the code bytes), run in LNSym, a Lean model of AArch64.

Each says: if the call is well formed (`Pre`, Spec.lean), running the code for
the stated number of steps returns to the caller with `Post` (Spec.lean):
`dst` holds `src` XOR the AES-CTR keystream, no other memory changed, and the
registers Go reserves are unchanged.
-/
import AesCtr.Final.CtrBlocks1Proof
import AesCtr.Proof.CtrBlocks2
import AesCtr.Proof.CtrBlocks4
import AesCtr.Proof.CtrBlocks8
import AesCtr.Bulk.PlainMain
import AesCtr.Bulk.Eor3Main
import AesCtr.KAT

namespace AesCtr

open Bulk in
/-- `ctrBlocksBulkAsm(nr, xk, dst, src, n, r, ivlo, ivhi)`: `12 n + r` blocks,
for any `n` and `r < 12`, provided the low 64 bits of the counter do not wrap
(the Go caller checks that they do not). -/
theorem ctrBlocksBulkAsm_correct (s0 : ArmState) (h : Pre plainProgram 8 (callBulk 12 s0) s0)
    (h_r : (arg s0 5).toNat < 12)
    (h_nowrap : (callBulk 12 s0).ivlo.toNat + (callBulk 12 s0).nblocks ≤ 2 ^ 64) :
    Post (callBulk 12 s0) s0
      (run (plainSteps (callBulk 12 s0).nr (arg s0 4).toNat (arg s0 5).toNat) s0) :=
  plain_correct s0 h h_r h_nowrap

open Bulk in
/-- `ctrBlocksBulkEOR3Asm`: the same, for the variant that uses EOR3. -/
theorem ctrBlocksBulkEOR3Asm_correct (s0 : ArmState) (h : Pre eor3Program 8 (callBulk 12 s0) s0)
    (h_r : (arg s0 5).toNat < 12)
    (h_nowrap : (callBulk 12 s0).ivlo.toNat + (callBulk 12 s0).nblocks ≤ 2 ^ 64) :
    Post (callBulk 12 s0) s0
      (run (eor3Steps (callBulk 12 s0).nr (arg s0 4).toNat (arg s0 5).toNat) s0) :=
  eor3_correct s0 h h_r h_nowrap

open Final in
/-- `ctrBlocks1Asm(nr, xk, dst, src, ivlo, ivhi)`: one block (any counter, it
carries across the 64-bit halves). -/
theorem ctrBlocks1Asm_correct (s0 : ArmState) (h : Pre ctrBlocks1Program 6 (callN s0 1) s0) :
    Post (callN s0 1) s0 (run (ctrBlocks1Steps (callN s0 1).nr) s0) :=
  ctrBlocks1_correct s0 h

open Base in
/-- `ctrBlocks2Asm(nr, xk, dst, src, ivlo, ivhi)` as on master: two blocks (any
counter). -/
theorem ctrBlocks2Asm_correct (s0 : ArmState) (h : Pre ctrBlocks2Program 6 (callN s0 2) s0) :
    Post (callN s0 2) s0 (run (ctrBlocks2Steps (callN s0 2).nr) s0) :=
  ctrBlocks2_correct s0 h

open Base in
/-- `ctrBlocks4Asm` as on master: four blocks (any counter). -/
theorem ctrBlocks4Asm_correct (s0 : ArmState) (h : Pre ctrBlocks4Program 6 (callN s0 4) s0) :
    Post (callN s0 4) s0 (run (ctrBlocks4Steps (callN s0 4).nr) s0) :=
  ctrBlocks4_correct s0 h

open Base in
/-- `ctrBlocks8Asm` as on master: eight blocks (any counter). -/
theorem ctrBlocks8Asm_correct (s0 : ArmState) (h : Pre ctrBlocks8Program 6 (callN s0 8) s0) :
    Post (callN s0 8) s0 (run (ctrBlocks8Steps (callN s0 8).nr) s0) :=
  ctrBlocks8_correct s0 h

end AesCtr
