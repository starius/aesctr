import re, sys, statistics, collections
# Usage: asm_table.py out.txt  -> median ns/op per (key, nb, mode) x function
d = collections.defaultdict(list)
for line in open(sys.argv[1]):
    m = re.match(r"BenchmarkExpAsm/(\d+)/(\d+)/(\w+)/(\w+)\S*\s+\d+\s+([\d.]+) ns/op", line)
    if m:
        k, nb, mode, f, ns = m.groups()
        d[(int(k), int(nb), mode, f)].append(float(ns))
        continue
    m = re.match(r"BenchmarkExpStream/(\d+)/(\d+)\S*\s+\d+\s+([\d.]+) ns/op", line)
    if m:
        k, nb, ns = m.groups()
        d[(int(k), int(nb), "stream", "cl")].append(float(ns))
funcs = ["fixed", "cl", "pairs", "ld4", "pre", "align", "clE3", "e3pairs", "e3ld4", "e3pre"]
present = [f for f in funcs if any(key[3] == f for key in d)]
rows = sorted({key[:3] for key in d}, key=lambda r: (r[0], r[2], r[1]))
n = max(len(v) for v in d.values())
print("median ns/op over up to %d rounds; columns: %s" % (n, " ".join(present)))
for r in rows:
    cells = []
    for f in present:
        v = d.get(r + (f,))
        cells.append("%7.2f" % statistics.median(v) if v else "      -")
    print("%3d %2d %-8s %s" % (r[0], r[1], r[2], " ".join(cells)))
