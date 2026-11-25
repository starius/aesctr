#!/usr/bin/env python3
# Experiment 3: the assembly called from xorKeyStreamAt directly, with the
# wrap and no-AES cases left to master's loop; plus tail variants of the
# generator. Usage: make-else-variants.py <workdir> exp/tail/genbulk_variant.go.txt
import os, shutil, subprocess, sys

W = sys.argv[1]
GENBULK = open(sys.argv[2]).read()
PKG = "src/crypto/internal/fips140/aes"

BULK = """\tif n := uint64(len(src)) / BlockSize; ctrBulk && supportsAES && n > 0 && n-1 <= ^ivlo {
\t\t// All full blocks in one call, unless the low 64 bits of the counter
\t\t// wrap within them.
\t\tif supportsAESEOR3 {
\t\t\tctrBlocksBulkEOR3Asm(c.b.rounds, &c.b.enc, &dst[0], &src[0], int(n/12), int(n%12), ivlo, ivhi)
\t\t} else {
\t\t\tctrBlocksBulkAsm(c.b.rounds, &c.b.enc, &dst[0], &src[0], int(n/12), int(n%12), ivlo, ivhi)
\t\t}
\t\tsrc = src[n*BlockSize:]
\t\tdst = dst[n*BlockSize:]
\t\tivlo, ivhi = add128(ivlo, ivhi, n)
\t}
"""

LOOP = "\tfor len(src) >= 8*BlockSize {\n"


def run(*a, **k):
    subprocess.run(a, check=True, **k)


def make(name, base, fall=True, tail=None, exit_=False):
    dst = os.path.join(W, "go-x3-" + name)
    if os.path.exists(dst):
        shutil.rmtree(dst)
    run("cp", "-a", os.path.join(W, "go-new"), dst)
    ctr = os.path.join(dst, PKG, "ctr.go")
    if fall:
        # master's ctr.go with the bulk call inserted before its loop.
        t = open(os.path.join(W, "go-base", PKG, "ctr.go")).read()
        assert t.count(LOOP) == 1
        t = t.replace(LOOP, BULK + "\n" + LOOP)
    else:
        t = open(ctr).read()
        old_head = "\tif ctrBulk {\n\t\t// All full blocks in one call.\n\t\tif n := uint64(len(src)) / BlockSize; n > 0 {\n\t\t\tctrBlocksBulk(&c.b, dst, src, n, ivlo, ivhi)\n\t\t\tsrc = src[n*BlockSize:]\n\t\t\tdst = dst[n*BlockSize:]\n\t\t\tivlo, ivhi = add128(ivlo, ivhi, n)\n\t\t}\n\t} else {\n"
        assert t.count(old_head) == 1
        t = t.replace(old_head, BULK[:-3] + "\t} else {\n")
    open(ctr, "w").write(t)
    if tail or exit_:
        g = os.path.join(dst, PKG, "ctr_arm64_gen.go")
        s = open(g).read()
        i = s.index("// genBulk writes")
        s = s[:i] + GENBULK
        s += '\nconst bulkTail = "%s"\n\nconst bulkExit = %s\n' % (tail or "pairs", "true" if exit_ else "false")
        open(g, "w").write(s)
        out = subprocess.run([os.path.join(dst, "bin/go"), "run", "ctr_arm64_gen.go"],
                             cwd=os.path.join(dst, PKG), check=True, capture_output=True, text=True).stdout
        open(os.path.join(dst, PKG, "ctr_arm64.s"), "w").write(out)
    print("made", dst)


make("fall", "go-new")
make("else", "go-new", fall=False)
make("pre", "go-new", tail="pre")
make("ld4", "go-new", tail="ld4")
make("exit", "go-new", exit_=True)
