import re, sys, statistics, collections, os
# Usage: cmp.py <dir> base v1 v2 ...  -> median sec/op change vs base, per benchmark
d = sys.argv[1]; base = sys.argv[2]; vs = sys.argv[3:]
def load(v):
    r = collections.defaultdict(list)
    for line in open(os.path.join(d, v + ".txt")):
        m = re.match(r"Benchmark(AESCTR\S*?)(?:-\d+)?\s+\d+\s+([\d.]+) ns/op", line)
        if m: r[m.group(1)].append(float(m.group(2)))
    return r
B = load(base); V = [load(v) for v in vs]
n = min(len(x) for x in B.values())
print("rounds:", n, "| base ns/op, then % change of median vs base:", " ".join(vs))
for k in B:
    b = statistics.median(B[k])
    cells = []
    for x in V:
        if k in x: cells.append("%+6.1f" % (100 * (statistics.median(x[k]) / b - 1)))
        else: cells.append("     -")
    print("%-22s %8.2f %s" % (k, b, " ".join(cells)))
