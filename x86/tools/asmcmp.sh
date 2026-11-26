#!/bin/bash
# Assemble <text.S> (the function's instructions and labels) with GNU as at
# <address> and compare its bytes with <func.bin>. Exits 1 on any difference.
# Usage: asmcmp.sh <text.S> <func.bin> <address hex> <layout.txt> <work dir>
set -euo pipefail
text=$1 func=$2 addr=$3 layout=$4 work=$5
mkdir -p "$work"
{ printf '  .text\n  .globl f\nf:\n'; cat "$text"; printf '\n'; } > "$work/in.S"
as --64 -o "$work/in.o" "$work/in.S"
ld -o "$work/in.elf" -Ttext="0x$addr" -e f "$work/in.o"
objcopy -O binary --only-section=.text "$work/in.elf" "$work/in.bin"
if cmp -s "$func" "$work/in.bin"; then
  echo "BYTES OK: $(stat -c %s "$func") bytes identical ($text)"
  exit 0
fi
echo "BYTES MISMATCH ($text)"
python3 - "$addr" "$func" "$work/in.bin" "$layout" <<'PY'
import sys
base, fa, fb, lay = int(sys.argv[1], 16), sys.argv[2], sys.argv[3], sys.argv[4]
a, b = open(fa, "rb").read(), open(fb, "rb").read()
print("sizes:", len(a), len(b))
bad = 0
for f in (l.split() for l in open(lay)):
    addr, n = int(f[0], 16), int(f[1])
    o = addr - base
    if a[o:o+n] != b[o:o+n]:
        bad += 1
        if bad <= 20:
            print("%x: go %s  as %s" % (addr, a[o:o+n].hex(), b[o:o+n].hex()))
print("instructions that differ:", bad)
PY
exit 1
