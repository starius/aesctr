#!/usr/bin/env bash
# Usage: run-h.sh: on every VM, run the correctness tests of the h and d1
# binaries, then the 5-way benchmark (8 rounds of 0.5s), in parallel.
W=/root/aesctr
K=(-i $W/gcp_key -o BatchMode=yes -o StrictHostKeyChecking=accept-new -o ConnectTimeout=30)
one() {
  name=$1; ip=$2
  {
    for v in x86-h1 x86-h2 x86-d1; do
      scp "${K[@]}" -q $W/out/$v/aes.test bench@$ip:$v-aes.test
      scp "${K[@]}" -q $W/out/$v/cipher.test bench@$ip:$v-cipher.test
      ssh "${K[@]}" bench@$ip "./$v-aes.test -test.run 'TestCTRBlocksBulk' -test.v 2>&1 | grep -E '^(--- |ok|FAIL|PASS)|skipping' ; ./$v-cipher.test -test.run 'CTR' 2>&1 | tail -1" | sed "s/^/$v: /"
    done
    $(dirname "$0")/bench.sh $ip x86h-$name 8 0.5s x86-base x86-g x86-d1 x86-h1 x86-h2
  } > $W/results-x86h-$name.log 2>&1
}
while read name ip _; do
  one $name $ip &
done < $W/vms-x86.txt
wait
echo all-done >> $W/results-x86h-all.log
