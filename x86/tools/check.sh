#!/bin/bash
# Checks the amd64 proofs against a test binary of crypto/internal/fips140/aes
# (go test -c -o aes.test crypto/internal/fips140/aes, on the Go change):
#  - converts the five CTR functions to assembly text (dis2kraken.py) and
#    checks that GNU as turns the text back into the bytes of the binary;
#  - regenerates asm/*.S and the generated Lean files and checks that they are
#    the ones in the repository;
#  - builds the proofs, checks that the programs Kraken parsed, printed by
#    Kraken, assemble to the same bytes, checks the axioms (Audit.lean) and
#    runs the evaluator tests.
# Stops at the first failure. Usage: tools/check.sh <aes.test>
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
root=$(dirname "$here")
bin=$(realpath "$1")
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
pkg=crypto/internal/fips140/aes

python3 "$here/dis2kraken.py" "$bin" "$work" \
  ctr1=$pkg.ctrBlocks1Asm.abi0 ctr2=$pkg.ctrBlocks2Asm.abi0 \
  ctr4=$pkg.ctrBlocks4Asm.abi0 ctr8=$pkg.ctrBlocks8Asm.abi0 \
  bulk=$pkg.ctrBlocksBulkAsm.abi0
while read -r name addr size; do
  bash "$here/asmcmp.sh" "$work/$name.S" "$work/$name.bin" "$addr" "$work/$name.layout" \
    "$work/as-$name"
  cmp "$work/$name.S" "$root/asm/$name.S"
done < "$work/funcs.txt"

python3 "$here/gen_lean.py" "$work" "$work/Layout.lean" "$work/Blocks.lean"
python3 "$here/gen_groups.py" "$work/NIGroups.lean" "$work/VGroups.lean"
python3 "$here/gen_fixed.py" "$work/FRuns.lean"
for f in Layout Blocks NIGroups VGroups FRuns; do
  cmp "$work/$f.lean" "$root/AesCtrX86/$f.lean"
done
echo "generated files ok"

cd "$root"
lake build
while read -r name addr size; do
  .lake/build/bin/aesctr_print "$name" > "$work/$name.parsed.S"
  bash "$here/asmcmp.sh" "$work/$name.parsed.S" "$work/$name.bin" "$addr" "$work/$name.layout" \
    "$work/as-parsed-$name"
done < "$work/funcs.txt"
lake env lean Audit.lean
echo "audit ok"
.lake/build/bin/aesctr_eval | tail -1
echo ALL-OK
