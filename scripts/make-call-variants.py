#!/usr/bin/env python3
# Experiment 2: Go-only variants of the CL, each in its own copy of the
# go-new tree (the change as first committed). Usage: make-call-variants.py <workdir>
import os, shutil, subprocess, sys

W = sys.argv[1]
SRC = os.path.join(W, "go-new")
PKG = "src/crypto/internal/fips140/aes"

CALL = "\t\t\tctrBlocksBulk(&c.b, dst, src, n, ivlo, ivhi)\n"

FIXED = {
    1: "\t\t\t\tctrBlocks1(&c.b, (*[BlockSize]byte)(dst), (*[BlockSize]byte)(src), ivlo, ivhi)\n",
    2: "\t\t\t\tctrBlocks2(&c.b, (*[2 * BlockSize]byte)(dst), (*[2 * BlockSize]byte)(src), ivlo, ivhi)\n",
    4: "\t\t\t\tctrBlocks4(&c.b, (*[4 * BlockSize]byte)(dst), (*[4 * BlockSize]byte)(src), ivlo, ivhi)\n",
    8: "\t\t\t\tctrBlocks8(&c.b, (*[8 * BlockSize]byte)(dst), (*[8 * BlockSize]byte)(src), ivlo, ivhi)\n",
}

DIRECT = """\t\t\t\tif supportsAES && n-1 <= ^ivlo {
\t\t\t\t\tif supportsAESEOR3 {
\t\t\t\t\t\tctrBlocksBulkEOR3Asm(c.b.rounds, &c.b.enc, &dst[0], &src[0], int(n/12), int(n%12), ivlo, ivhi)
\t\t\t\t\t} else {
\t\t\t\t\t\tctrBlocksBulkAsm(c.b.rounds, &c.b.enc, &dst[0], &src[0], int(n/12), int(n%12), ivlo, ivhi)
\t\t\t\t\t}
\t\t\t\t} else {
\t\t\t\t\tctrBlocksBulkSlow(&c.b, dst, src, n, ivlo, ivhi)
\t\t\t\t}
"""


def indent(s, k=1):
    return "".join("\t" * k + line if line.strip() else line for line in s.splitlines(True))


def switch(cases, default):
    out = "\t\t\tswitch n {\n"
    for n in cases:
        out += "\t\t\tcase %d:\n" % n + FIXED[n]
    out += "\t\t\tdefault:\n" + default
    out += "\t\t\t}\n"
    return out


variants = {
    "fix4": {"ctr.go": switch([4], "\t" + CALL)},
    "fixall": {"ctr.go": switch([1, 2, 4, 8], "\t" + CALL)},
    "direct": {"ctr.go": DIRECT.replace("\t\t\t\t", "\t\t\t", 1).replace("\n\t\t\t\t", "\n\t\t\t")},
    "directfix": {"ctr.go": switch([1, 2, 4, 8], DIRECT)},
}

NODIV_OLD = """\tif supportsAESEOR3 {
\t\tctrBlocksBulkEOR3Asm(b.rounds, &b.enc, &dst[0], &src[0], int(n/12), int(n%12), ivlo, ivhi)
\t} else {
\t\tctrBlocksBulkAsm(b.rounds, &b.enc, &dst[0], &src[0], int(n/12), int(n%12), ivlo, ivhi)
\t}
"""
NODIV_NEW = """\tq, r := 0, int(n)
\tif n >= 12 {
\t\tq, r = int(n/12), int(n%12)
\t}
\tif supportsAESEOR3 {
\t\tctrBlocksBulkEOR3Asm(b.rounds, &b.enc, &dst[0], &src[0], q, r, ivlo, ivhi)
\t} else {
\t\tctrBlocksBulkAsm(b.rounds, &b.enc, &dst[0], &src[0], q, r, ivlo, ivhi)
\t}
"""

for name, files in list(variants.items()) + [("nodiv", None)]:
    dst = os.path.join(W, "go-x2-" + name)
    if os.path.exists(dst):
        shutil.rmtree(dst)
    subprocess.run(["cp", "-a", SRC, dst], check=True)
    if name == "nodiv":
        p = os.path.join(dst, PKG, "ctr_arm64.go")
        t = open(p).read()
        assert t.count(NODIV_OLD) == 1, name
        open(p, "w").write(t.replace(NODIV_OLD, NODIV_NEW))
        continue
    p = os.path.join(dst, PKG, "ctr.go")
    t = open(p).read()
    assert t.count(CALL) == 1, name
    open(p, "w").write(t.replace(CALL, files["ctr.go"]))
    print("made", dst)
print("made", os.path.join(W, "go-x2-nodiv"))
