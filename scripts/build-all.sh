#!/usr/bin/env bash
# Build every proof (in the dev shell, from proj/). The per-group lemmas of the
# two bulk functions dominate (about an hour); they and the other proofs build
# as three disjoint pipelines once the shared modules are built.
# Logs: out/all-*.log.
set -uo pipefail
L="$(pwd)/out"
mkdir -p "$L"
cd lean
echo "shared: $(date +%T)"
lake build AesCtr.Spec AesCtr.Lemmas AesCtr.ProofLib AesCtr.Loop AesCtr.Compose AesCtr.KAT \
  AesCtr.Bulk.PlainLayout AesCtr.Bulk.Eor3Layout AesCtr.Bulk.PlainSteps AesCtr.Bulk.Eor3Steps \
  > $L/all-shared.log 2>&1 || { echo "shared failed"; grep -E "^error" $L/all-shared.log | head; exit 1; }
cd ..
echo "pipelines: $(date +%T)"
bash scripts/build-groups.sh lean/AesCtr/Bulk AesCtr.Bulk Eor3 eor3 eor3Program eor3Layout 29,30,31 4 > $L/all-groups-eor3.log 2>&1 &
bash scripts/build-groups.sh lean/AesCtr/Bulk AesCtr.Bulk Plain plain plainProgram plainLayout 29,30,31 4 > $L/all-groups-plain.log 2>&1 &
(cd lean && lake build AesCtr.Bulk.PlainCtl AesCtr.Bulk.Eor3Ctl AesCtr.Final.CtrBlocks1Proof \
  AesCtr.Proof.CtrBlocks1 AesCtr.Proof.CtrBlocks2 AesCtr.Proof.CtrBlocks4 AesCtr.Proof.CtrBlocks8 \
  > $L/all-other.log 2>&1; echo "other exit $?") &
wait
echo "root: $(date +%T)"
cd lean
# The root module imports every proof except the one of master's
# ctrBlocks1Asm, which has the same instruction words as Final/.
if lake build AesCtr AesCtr.Proof.CtrBlocks1 > $L/all-root.log 2>&1; then
  echo "root succeeded $(date +%T)"
else
  echo "root failed $(date +%T)"
  grep -E "^error|^✖" $L/all-root.log | head -20 || true
  exit 1
fi
