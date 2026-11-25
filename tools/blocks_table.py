#!/usr/bin/env python3
r"""Summarize BenchmarkAESCTRBlocks results as the table of the Go change.

Usage: blocks_table.py <v2.csv> <n3.csv> <n1.csv>

Each file is the CSV that benchstat prints for one CPU (Neoverse-V2, N3, N1):

  benchstat -format csv -filter '.name:AESCTRBlocks .unit:B/s' \
      master=r7-base.txt new=r7-new.txt > blocks-bps.csv

Prints the change in B/s by number of blocks (rows) and CPU and key size
(columns), "~" where benchstat finds no significant difference, then the
ranges for exactly 1, 2, 4 or 8 blocks and for the other sizes.
"""
import sys
from decimal import Decimal, ROUND_HALF_UP

cpus = ["Neoverse-V2", "Neoverse-N3", "Neoverse-N1"]
keys = ["128", "192", "256"]
data = {}  # (cpu, key, blocks) -> (delta string, delta float or None, p)
for cpu, path in zip(cpus, sys.argv[1:4]):
    for line in open(path):
        f = line.rstrip("\n").split(",")
        if not f[0].startswith("AESCTRBlocks/"):
            continue
        _, key, blocks = f[0].split("/")
        delta, p = f[5], f[6]
        val = None if delta == "~" else float(delta.rstrip("%"))
        data[(cpu, key, int(blocks))] = (delta, val, p)

assert len(data) == 3 * 3 * 12, len(data)

def cell(cpu, key, b):
    d, v, p = data[(cpu, key, b)]
    if v is None:
        return "~"
    q = Decimal(d.rstrip("%")).quantize(Decimal("0.1"), rounding=ROUND_HALF_UP)
    return ("+" if q > 0 else "") + str(q) + "%"

w = 7
print("      " + "".join(("%-" + str(3 * w + 2) + "s") % ("  " + c) for c in cpus).rstrip())
print("blocks" + "".join("  " + "".join(k.rjust(w) for k in keys) for c in cpus))
for b in range(1, 13):
    print(str(b).rjust(6) + "".join("  " + "".join(cell(c, k, b).rjust(w) for k in keys) for c in cpus))

print()
for name, sel in [("exact 1/2/4/8", lambda b: b in (1, 2, 4, 8)), ("other", lambda b: b not in (1, 2, 4, 8))]:
    for c in cpus:
        vals = [data[(c, k, b)] for k in keys for b in range(1, 13) if sel(b)]
        nums = [v for _, v, _ in vals if v is not None]
        ns = sum(1 for _, v, _ in vals if v is None)
        print("%-14s %-12s min %+.2f%% max %+.2f%% non-significant %d" % (name, c, min(nums), max(nums), ns))
