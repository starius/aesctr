#!/usr/bin/env python3
"""Move the code addresses written in the generators and the hand-written
proofs by the same amount, for a binary in which the linker placed the
functions elsewhere (the data must be where it was).

Usage: relocate.py <old funcs.txt> <new funcs.txt> <file>...

Every hexadecimal number 0x<a> or name suffix _<a> with <a> in the code of the
old functions becomes the same with <a> + delta, where delta is the same for
all the functions (the script checks that).
"""
import re
import sys

def funcs(path):
    return [(l.split()[0], int(l.split()[1], 16), int(l.split()[2], 16)) for l in open(path)]

old, new = funcs(sys.argv[1]), funcs(sys.argv[2])
assert [(n, s) for n, _, s in old] == [(n, s) for n, _, s in new], "different functions"
deltas = {b - a for (_, a, _), (_, b, _) in zip(old, new)}
assert len(deltas) == 1, "the functions moved by different amounts"
delta = deltas.pop()
lo, hi = old[0][1], old[-1][1] + old[-1][2]

def move(m):
    a = int(m.group(2), 16)
    if lo <= a < hi:
        return "%s%x" % (m.group(1), a + delta)
    return m.group(0)

for path in sys.argv[3:]:
    s = open(path).read()
    t = re.sub(r"(0x|_)([0-9a-f]{6})\b", move, s)
    if t != s:
        open(path, "w").write(t)
        print("%s: moved by %#x" % (path, delta))
