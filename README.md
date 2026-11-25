# aesctr

Lean 4 proofs that Go's arm64 AES-CTR assembly (`crypto/internal/fips140/aes`)
computes AES-CTR, about the exact instruction words in the linked binary, run
in [LNSym](https://github.com/leanprover/LNSym) (a Lean model of AArch64).
Context: golang/go#76061.

## What is proved

`lean/AesCtr/Theorems.lean` has one theorem per assembly function the arm64
build calls:

- `ctrBlocksBulkAsm_correct`, `ctrBlocksBulkEOR3Asm_correct`: all full blocks
  of a message, `12 n + r` blocks for any `n` and any `r < 12`, provided the
  low 64 bits of the counter do not wrap (the Go caller splits the call there).
- `ctrBlocks1Asm_correct`: one block (used for a partial last block).

Each says: for any machine state that satisfies `Pre` (a well formed call),
running the code for the stated number of steps returns to the caller in a
state that satisfies `Post`. Both are in `lean/AesCtr/Spec.lean`, the contract.

`lean/AesCtr/Audit.lean` checks that the theorems use only Lean's standard
axioms (no `sorry`, no `native_decide`/`bv_decide`). `lean/AesCtr/KAT.lean`
checks the spec's AES against FIPS-197 C.1, C.2 and C.3.

## Layout

- `lean/AesCtr/Spec.lean`: the contract.
- `lean/AesCtr/Loop.lean`: the loop invariant of the bulk functions;
  `Compose.lean` composes `n` loop iterations.
- `lean/AesCtr/Bulk/`: the two bulk functions. `Plain.lean` and `Eor3.lean` are
  the programs (instruction words with both disassemblies as comments),
  `*Steps.lean` their step theorems, `G*.lean` one lemma per straight-line group
  (12 blocks, or 8/4/2/1 in the tail), `*Ctl.lean` the branches, prologue and
  return, `*Main.lean` the composition.
- `lean/AesCtr/Final/`: `ctrBlocks1Asm` of the new binary.
- `lean/AesCtr/Base/`, `Proof/`: `ctrBlocks{1,2,4,8}Asm` as on master (still in
  the assembly, no longer called on arm64).
- `tools/`: Python generators for the program files and the proof scripts.
  They only propose text: Lean checks the proofs. The statements in
  `Theorems.lean` are written by hand, and the program files are trusted (see
  below).
- `scripts/`: build and benchmark scripts. `exp/`: Go prototypes of the
  variants that were measured. `results/`: benchstat inputs and summaries.

## Performance

`results/r7-{v2,n3,n1}/benchstat.txt`: benchstat of master against the Go
change on Neoverse-V2 (GCP c4a), Neoverse-N3 (n4a) and Neoverse-N1 (t2a), 8
rounds that run the two test binaries in turn, with crypto/cipher's
`BenchmarkAESCTR` and the change's new `BenchmarkAESCTRBlocks` (messages of 1
to 12 whole blocks; master was measured with it added). The raw
`go test -bench` outputs are next to them. Geomean B/s of `BenchmarkAESCTR`:
+34.4%, +15.9%, +19.5%. Messages of exactly 1, 2, 4 or 8 blocks, which master
passes to one fixed-size function, change in throughput by -7.7% to +7.8%; the
other whole-block sizes gain 5.8% to 44.3%. `tools/blocks_table.py` makes the
table of these in the description of the Go change.

The change (`exp/aes6/`) has lower throughput than master for some short
messages. The experiments below compare the assembly and the Go code that
calls it, to look for the cause:

- `results/x1-*`: the assembly called directly in a loop (`exp/tail/`,
  `tools/asm_table.py`), master's fixed-size functions against the bulk
  functions and variants of their tail, in place, out of place and
  alternating two buffers. Called this way, the bulk EOR3 function is
  comparable to master's fixed-size functions or faster on Neoverse-V2 and
  N3, with a few small regressions; the three buffer arrangements give
  similar results.
- `results/x2-*`: Go-only variants of the call path, end to end
  (`scripts/make-call-variants.py`, `tools/median_cmp.py`). Calling
  master's fixed-size functions for those sizes does not help; calling the
  assembly from `xorKeyStreamAt` with no Go function in between does.
- `results/x3-*` (stopped after 2 or 3 of 8 rounds): the bulk call with
  master's loop in an `else` branch, or before it, and three tail variants
  (`scripts/make-else-variants.py`). The `else` form is best; the tail
  variants make no clear difference.

`results/final-*` and `results/r6-*` are earlier measurements of the change,
with the benchmarks of `exp/cipher/ctr_extra_test.go`; `results/r1-*` and
`results/r*-summary.txt` are from the experiments.

## Build

The builds are heavy: one group lemma takes up to about 16 minutes and several
GB, and there are 30. Run them on a build machine with Nix;
`scripts/build-all.sh` builds the group lemmas in batches (4 per function) to
bound memory, then the rest, ending with a build of the root module `AesCtr`
(which includes the axiom audit) and of the proof of master's `ctrBlocks1Asm`.
It exits with status 1 if a proof fails. About an hour on 16 cores and 30 GB:

    nix develop -c bash scripts/setup-vendor.sh
    nix develop -c bash scripts/build-all.sh

To regenerate a program file from a Go test binary:
`python3 tools/gen_program.py <binary> <symbol> <namespace> <name> <out.lean>`.

## Trusted, and not proved

Trusted: LNSym's model (instruction semantics, decoder, memory, byte order),
the Lean kernel, and that the program files are the linked code (checked by
re-extracting from the binary and comparing the words). The proofs place the
code at address 0; it uses only PC-relative branches, so the result carries to
any address, but that step is an argument, not a theorem. The model has no
faults, interrupts or concurrency.

Not proved: Go's key expansion (the theorems take the round keys in memory as
given), the Go code around the assembly (`ctr.go`, `ctr_arm64.go`: splitting at
the 64-bit wrap, `n/12` and `n%12`, which the Go tests cover), constant-time
execution, and performance.

## License

MIT (`LICENSE`). Files copied or adapted from the Go project (the Go code in
`exp/`, and the machine code of Go's assembly in the Lean program files) are
distributed under the terms in `LICENSE-Go`; the copied Go files keep their Go
Authors copyright notices.
