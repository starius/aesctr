#!/usr/bin/env bash
# Usage: bench.sh <ip> <tag> <rounds> <benchtime> <variant>...
# Ran on the build machine, with the test binaries under $W/out and a GCP
# VM at <ip> (user bench).
# Runs crypto/cipher AESCTR benchmarks of out/<variant>/cipher.test, the
# variants interleaved round by round, pinned to one core.
set -euo pipefail
ip=$1; tag=$2; rounds=$3; bt=$4; shift 4
W=/root/aesctr
K=(-i $W/gcp_key -o BatchMode=yes -o StrictHostKeyChecking=accept-new -o ConnectTimeout=30)
res=$W/results/$tag
mkdir -p $res
for v in "$@"; do
  scp "${K[@]}" -q $W/out/$v/cipher.test bench@$ip:$v.test
  : > $res/$v.txt
done
for i in $(seq $rounds); do
  for v in "$@"; do
    ssh "${K[@]}" bench@$ip "taskset -c 2 ./$v.test -test.run NONE -test.bench AESCTR -test.count 1 -test.benchtime $bt" \
      | grep -E "^(Benchmark|goos|goarch|pkg|cpu)" >> $res/$v.txt
  done
done
echo "done $tag"
