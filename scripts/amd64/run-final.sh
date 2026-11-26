#!/usr/bin/env bash
# Final master vs h1 benchmark on every VM: 10 rounds of 1s, in parallel.
# vms-x86.txt: one line per VM, its name and IP address.
W=/root/aesctr
while read name ip _; do
  $(dirname "$0")/bench.sh $ip x86j-$name 10 1s x86-base x86-h1 > $W/results-x86j-$name.log 2>&1 &
done < $W/vms-x86.txt
wait
echo all-done > $W/results-x86j-all.log
