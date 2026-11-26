#!/usr/bin/env python3
# Reads `go tool objdump` output on stdin and marks jumps hit by the Intel
# JCC erratum (SKX102): a jump, or a macro-fused cmp/test+jcc pair, that
# crosses or ends on a 32-byte boundary is not cached in the DSB.
import re, sys
fuse = re.compile(r'^(CMP|TEST|ADD|SUB|AND|INC|DEC)')
jmp = re.compile(r'^(J[A-Z]+|RET|CALL)\b')
prev = None
for line in sys.stdin:
    if line.startswith('TEXT'):
        print(line.rstrip()); prev = None; continue
    f = [x for x in line.rstrip("\n").split("\t") if x.strip()]
    if len(f) < 4:
        continue
    loc, addr, hexb, ins = f[0].strip(), int(f[1], 16), f[2], f[3].strip()
    n = len(hexb) // 2
    tag = ''
    if jmp.match(ins):
        start = addr
        if prev and fuse.match(prev[3]) and ins.startswith('J') and not ins.startswith('JMP') and prev[1] + prev[2] == addr:
            start = prev[1]
        end = addr + n
        if start // 32 != (end - 1) // 32 or end % 32 == 0:
            tag = '  <== JCC erratum (start %#x end %#x)' % (start, end)
    print('%s %#x %2d %-40s%s' % (loc.split(':')[-1].rjust(5), addr, n, ins, tag))
    prev = (loc, addr, n, ins)
