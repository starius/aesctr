#!/usr/bin/env python3
"""Turn the linked CTR functions into assembly text for Kraken and GNU as.

Usage: dis2kraken.py <go test binary> <out dir> <name>=<symbol>...

For each function <name>, writes to <out dir>:
  <name>.S       the function as AT&T assembly with labels, for Kraken's parser
  <name>.layout  one line per instruction: address, length, label (if any)
  <name>.bin     the function's bytes, from the binary
and also:
  funcs.txt      one line per function: name, address, size
  data.txt       the bytes of bswapMask and ctrOffsets, from the binary

The functions must be given in address order. Jump targets become labels
L<address>. RIP-relative operands keep the binary's displacement (the fork's
parser does not accept a symbol there); the script checks that each one
points to bswapMask or to the start of a 16-byte entry of ctrOffsets.
"""
import re, subprocess, sys

binary, out = sys.argv[1:3]
funcs = [a.split("=", 1) for a in sys.argv[3:]]

def run(*args):
    return subprocess.run(args, check=True, capture_output=True, text=True).stdout

# Symbols: address and size.
syms = {}
for line in run("nm", "-S", binary).splitlines():
    f = line.split(maxsplit=3)
    if len(f) == 4:
        syms[f[3]] = (int(f[0], 16), int(f[1], 16))
data = {name: syms[name] for name in ("bswapMask", "ctrOffsets")}

# Section bytes: read the file at the section's offset.
def read_vaddr(addr, n):
    for line in run("readelf", "-W", "-S", binary).splitlines():
        m = re.match(r"\s*\[\s*\d+\]\s+(\S+)\s+\S+\s+([0-9a-f]+)\s+([0-9a-f]+)\s+([0-9a-f]+)", line)
        if not m:
            continue
        va, off, size = (int(x, 16) for x in m.group(2, 3, 4))
        if va <= addr and addr + n <= va + size and va != 0:
            with open(binary, "rb") as fh:
                fh.seek(off + addr - va)
                return fh.read(n)
    raise SystemExit("address %#x not in a section" % addr)

def data_label(target):
    a, n = data["bswapMask"]
    if target == a:
        return "bswapMask"
    a, n = data["ctrOffsets"]
    if a <= target < a + n and (target - a) % 16 == 0:
        return "ctrOffsets_%d" % ((target - a) // 16)
    raise SystemExit("RIP-relative reference to %#x" % target)

def convert(name, func):
    faddr, fsize = syms[func]
    open("%s/%s.bin" % (out, name), "wb").write(read_vaddr(faddr, fsize))

    dis = run("objdump", "-d", "-w", "--disassemble=" + func, binary)
    insns = []  # (addr, length, mnemonic, operands, comment)
    for line in dis.splitlines():
        m = re.match(r"\s+([0-9a-f]+):\t((?:[0-9a-f]{2} )+)\s*\t(\S+)\s*(.*)$", line)
        if not m:
            continue
        addr = int(m.group(1), 16)
        n = len(m.group(2).split())
        mnem, rest = m.group(3), m.group(4)
        comment = ""
        if "#" in rest:
            rest, comment = rest.split("#", 1)
        insns.append((addr, n, mnem, rest.strip(), comment.strip()))

    # Every byte of the function belongs to exactly one instruction.
    pos = faddr
    for addr, n, *_ in insns:
        assert addr == pos, "gap or overlap at %#x" % addr
        pos += n
    assert pos == faddr + fsize, "function size %#x, instructions end at %#x" % (fsize, pos)

    targets = set()
    lines = []
    for addr, n, mnem, ops, comment in insns:
        if mnem.startswith("j"):
            m = re.match(r"([0-9a-f]+) <", ops)
            t = int(m.group(1), 16)
            assert faddr <= t < faddr + fsize
            targets.add(t)
            ops = "L%x" % t
        elif "(%rip)" in ops:
            m = re.match(r"([0-9a-f]+) <", comment)
            t = int(m.group(1), 16)
            disp = re.search(r"(-?0x[0-9a-f]+)\(%rip\)", ops)
            assert int(disp.group(1), 16) == t - (addr + n), "RIP target mismatch at %#x" % addr
            data_label(t)
        lines.append((addr, n, "%s %s" % (mnem, ops) if ops else mnem))

    with open("%s/%s.S" % (out, name), "w") as k, open("%s/%s.layout" % (out, name), "w") as lay:
        for addr, n, text in lines:
            label = "L%x" % addr if addr in targets else ""
            if label:
                k.write("%s:\n" % label)
            k.write("  %s\n" % text)
            lay.write("%x %d %s\n" % (addr, n, label))
    print("%s: %d instructions, %d bytes, %d labels" % (name, len(insns), fsize, len(targets)))
    return faddr, fsize

with open(out + "/funcs.txt", "w") as ft:
    prev_end = 0
    for name, func in funcs:
        faddr, fsize = convert(name, func)
        assert faddr >= prev_end, "functions must be in address order"
        prev_end = faddr + fsize
        ft.write("%s %x %x\n" % (name, faddr, fsize))

with open(out + "/data.txt", "w") as d:
    for name in ("bswapMask", "ctrOffsets"):
        a, n = data[name]
        d.write("%s %x %s\n" % (name, a, read_vaddr(a, n).hex()))
