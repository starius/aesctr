#!/usr/bin/env bash
# Run crypto/cipher's AES-CTR benchmarks for several variants on a benchmark
# VM, interleaving the variants round by round to spread out drift.
# Usage: bench.sh <ip> <tag> <rounds> <variant>...
# Results: /root/aesctr/results/<tag>/<variant>.txt (benchstat input).
set -euo pipefail
ip=$1; tag=$2; rounds=$3; shift 3
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
    ssh "${K[@]}" bench@$ip "taskset -c 2 ./$v.test -test.run NONE -test.bench 'AESCTR' -test.count 1 -test.benchtime 1s" \
      | grep -E "^(Benchmark|goos|goarch|pkg|cpu)" >> $res/$v.txt
  done
done
echo "done $tag"
