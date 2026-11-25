/-
What is proved, in one place.

On arm64, crypto/internal/fips140/aes runs three assembly functions for CTR:
`ctrBlocksBulkAsm` or `ctrBlocksBulkEOR3Asm` (with FEAT_SHA3) for all full
blocks, and `ctrBlocks1Asm` for a partial block. Each theorem below is about
the exact instruction words the Go toolchain emits for that function (see
`Bulk/Plain.lean`, `Bulk/Eor3.lean`, `Final/CtrBlocks1.lean`, generated from
the linked test binary, with the SHA-256 of the code bytes), run in LNSym, a
Lean model of AArch64.

Each says: if the call is well formed (`Pre`, Spec.lean), running the code for
the stated number of steps returns to the caller with `Post` (Spec.lean):
`dst` holds `src` XOR the AES-CTR keystream, no other memory changed, and the
registers Go reserves are unchanged.
-/
import AesCtr.Final.CtrBlocks1Proof
import AesCtr.Bulk.PlainMain
import AesCtr.Bulk.Eor3Main
import AesCtr.KAT

namespace AesCtr

open Bulk in
/-- `ctrBlocksBulkAsm(nr, xk, dst, src, n, r, ivlo, ivhi)`: `12 n + r` blocks,
for any `n` and `r < 12`, provided the low 64 bits of the counter do not wrap
(the Go caller splits the call where they would). -/
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

end AesCtr
