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
  low 64 bits of the counter do not wrap (the Go caller checks that).
- `ctrBlocks1Asm_correct`: one block (used for a partial block).
- `ctrBlocks2Asm_correct`, `ctrBlocks4Asm_correct`, `ctrBlocks8Asm_correct`:
  master's fixed-size functions, which the change leaves as they were. With
  `ctrBlocks1Asm`, the Go code still uses them for the full blocks of a
  message within which the low 64 bits of the counter would wrap.

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
- `lean/AesCtr/Base/`, `Proof/`: `ctrBlocks{1,2,4,8}Asm` as on master (the new
  binary has the same instruction words).
- `tools/`: Python generators for the program files and the proof scripts.
  They only propose text: Lean checks the proofs. The statements in
  `Theorems.lean` are written by hand, and the program files are trusted (see
  below).
- `scripts/`: build and benchmark scripts. `exp/`: Go prototypes of the
  variants that were measured. `results/`: benchstat inputs and summaries.

## Performance

`results/r9-{v2,n3,n1}/benchstat.txt`: benchstat of master against the Go
change on Neoverse-V2 (GCP c4a), Neoverse-N3 (n4a) and Neoverse-N1 (t2a), 8
rounds that run the test binaries in turn, with crypto/cipher's
`BenchmarkAESCTR` and the change's new `BenchmarkAESCTRBlocks` (messages of 1
to 12 whole blocks; master was measured with it added). The raw
`go test -bench` outputs are next to them (`r9-base.txt` is master at
d695060f5b, `r9-new.txt` the change on top of it). Geomean B/s of
`BenchmarkAESCTR`: +38.1%, +16.9%, +20.4%. Messages of exactly 1, 2, 4 or 8
blocks, which master passes to one fixed-size function, change in throughput
by -2.7% to +9.5%: the only decreases are for 4 blocks on Neoverse-N1 (2.4% to
2.7%) and 8 blocks with AES-256 on Neoverse-V2 (0.2%). The other whole-block
sizes gain 8.4% to 46.2%. `tools/blocks_table.py` makes the table of these in
the description of the Go change.

`results/r8-*` is the same comparison on master d56a7e140c, before the change
was rebased (`r7-base.txt` is master, `cand.txt` the change, `r7-new.txt` the
change as first written).

The change as first written (`r7-*`; Go side in `exp/aes6/`) called the
assembly through a Go function that chose the variant, split the call where
the counter wrapped, and computed `n/12` and `n%12`. With it, messages of
exactly 1, 2, 4 or 8 blocks had throughput decreases of up to 7.7% against
master. The experiments that looked for the cause:

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
  variants make no clear difference, so the proved assembly stays.

`exp/aes7/` is the Go side of the change now. `results/final-*` and
`results/r6-*` are earlier measurements of the change, with the benchmarks of
`exp/cipher/ctr_extra_test.go`; `results/r1-*` and `results/r*-summary.txt`
are from the experiments that led to the bulk functions.

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
given), the Go code around the assembly (`ctr.go`, `ctr_arm64.go`: the choice
between the bulk and the fixed-size functions, `n/12` and `n%12`, which the Go
tests cover), constant-time execution, and performance.

## amd64

On amd64, the change replaces the calls of master's `ctrBlocks8Asm` for every
8 blocks (then `ctrBlocks4Asm`, `ctrBlocks2Asm` and `ctrBlocks1Asm` for the
rest) with one assembly call for all full blocks, `ctrBlocksBulkAsm`,
generated with avo. On CPUs with VAES and AVX2 it encrypts two blocks per
instruction in YMM registers, 16 blocks per loop iteration; otherwise it uses
AES-NI, 8 blocks per iteration. Master's fixed-size functions stay for a
partial block and for messages within which the low 64 bits of the counter
wrap.

### amd64 performance

`results/x86jd-<cpu>/benchstat.txt`: benchstat of master (d695060f5b) against
the change on top of it, 10 rounds of 1 s that run the test binaries in turn
(`scripts/amd64/run-final.sh`, `scripts/amd64/bench.sh`), pinned to one core,
on GCP n2d (AMD Zen 2, `zen2`), n2 (Intel Cascade Lake, `clx`), t2d (AMD Zen
3, `zen3`), c3d (AMD Zen 4, `zen4`), n2 (Intel Ice Lake, `icx`) and c3
(Intel Sapphire Rapids, `spr`). The first two have no VAES and use the AES-NI
path. Geomean B/s of `BenchmarkAESCTR`: +10.7%, +17.2%, +58.9%, +54.0%,
+83.2% and +58.3%. Messages of exactly 1, 2, 4 or 8 blocks, which master
passed to one fixed-size function, change in throughput by +0.2% to +7.1% on
Zen 2, -5.7% to +5.2% on Cascade Lake, -0.6% to +18.0% on Zen 3, -1.5% to
+25.1% on Zen 4, +1.4% to +31.3% on Ice Lake and +0.8% to +26.4% on Sapphire
Rapids; the other whole-block sizes measured change by -1.3% to +62.2%. The
raw outputs are in `results/x86j-<cpu>/` (`x86-base.txt` is master,
`x86-h1.txt` the change); the tables in the description of the Go change come
from these.

The rounds before it (the `d` directories hold the benchstat tables of the
run of the same name without `d`):

- `results/x86a-summary.txt`: the first variants, written into a Go tree by
  `scripts/amd64/make_exp.py` (the generator and the glue are in
  `exp/amd64/variants/`): AES-NI with 8 blocks per iteration, with and
  without the source folded into the last round key (`xmm8f`, `xmm8`); VAES
  on YMM registers with 4, 6 or 8 registers per iteration (`ymm4f`, `ymm6f`,
  `ymm8f`, `ymm8`); VAES on ZMM registers (`zmm*`) and on EVEX-encoded YMM
  registers (`ey*`), which need AVX-512. `master-` is master's loop in the
  experiment's tree. The change uses `xmm8f` and `ymm8f`: the AVX-512
  variants were faster for 8 KiB messages, but slower for one or two blocks
  on Ice Lake.
- `results/x86f-*`: the first full version of the change against master.
- `results/x86g-*`, `x86gd-*`: version g (`exp/amd64/g/`), which made short
  messages faster, against f and master.
- `results/x86h-*`, `x86hd-*` (`scripts/amd64/build-h.sh`, `run-h.sh`): g;
  d1, which is g leaving messages of fewer than 8 blocks to master's
  functions on CPUs without VAES; h1 (`exp/amd64/h1/`), in which each group
  of the tail adds its counter step from `ctrOffsets` and advances the
  pointers only when another group follows; and h2, h1 with the tail before
  the loop. h1 is the change. `results/jcc-*.txt` mark the branch layouts of g,
  h1, h2 and master's functions that Intel's JCC erratum may affect
  (`scripts/amd64/jcc.py`).

## License

MIT (`LICENSE`). Files copied or adapted from the Go project (the Go code in
`exp/`, and the machine code of Go's assembly in the Lean program files) are
distributed under the terms in `LICENSE-Go`; the copied Go files keep their Go
Authors copyright notices.
