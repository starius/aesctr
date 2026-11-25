#!/usr/bin/env bash
# Generate one Lean file per group lemma and build them in batches (memory).
# Usage (in the dev shell, from proj/):
#   build-groups.sh <dir> <ns> <Prog-file-stem> <prefix> <prog> <layout> <regs> <batch>
# e.g. build-groups.sh lean/AesCtr/Bulk AesCtr.Bulk Eor3 eor3 eor3Program eor3Layout 29,30,31 5
set -uo pipefail
D=$1; ns=$2; stem=$3; P=$4; prog=$5; layout=$6; regs=$7; batch=${8:-5}
Pc="$(echo "${P:0:1}" | tr a-z A-Z)${P:1}"
moddir=$(echo "${D#lean/}" | tr / .)
mods=()
while read -r g; do
  [ -z "$g" ] && continue
  name=${g%%:*}
  N=$(echo "$name" | sed 's/^./\U&/; s/_\(.\)/\U\1/g')
  python3 tools/gen_bulk_proof2.py $D/$stem.lean $ns $prog $layout 26 $regs $D/G$N.lean "$g"
  mods+=("$moddir.G$N")
done < $D/${Pc}Groups.txt
log="$(pwd)/out/groups-batch-$P.log"
mkdir -p out
cd lean
for ((i = 0; i < ${#mods[@]}; i += batch)); do
  chunk=("${mods[@]:i:batch}")
  echo "=== ${chunk[*]}"
  t0=$(date +%s); lake build "${chunk[@]}" > "$log" 2>&1; echo "exit $? after $(( $(date +%s) - t0 )) s"
  grep -E "^error|Built $moddir.G" "$log" | head -20
done
echo "all done"
