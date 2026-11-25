#!/usr/bin/env bash
# Usage: bench-asm.sh <ip> <tag> <rounds> <binary> <bench regex> <benchtime>
# Runs one test binary on a benchmark VM, round by round, pinned to one core.
set -euo pipefail
ip=$1; tag=$2; rounds=$3; bin=$4; re=$5; bt=$6
W=/root/aesctr
K=(-i $W/gcp_key -o BatchMode=yes -o StrictHostKeyChecking=accept-new -o ConnectTimeout=30)
res=$W/results/$tag
mkdir -p $res
for i in 1 2 3 4 5 6 7 8 9 10; do ssh "${K[@]}" bench@$ip true 2>/dev/null && break; sleep 5; done
ssh "${K[@]}" bench@$ip "lscpu | grep -E \"Model name|MHz\" ; nproc" > $res/cpu.txt
scp "${K[@]}" -q $bin bench@$ip:x.test
: > $res/out.txt
for i in $(seq $rounds); do
  ssh "${K[@]}" bench@$ip "taskset -c 2 ./x.test -test.run NONE -test.bench \"$re\" -test.count 1 -test.benchtime $bt" \
    | grep -E "^(Benchmark|goos|goarch|pkg|cpu)" >> $res/out.txt
done
echo "done $tag"
