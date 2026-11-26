#!/usr/bin/env python3
# Writes the amd64 experiment glue into a Go tree (the aes-amd64 worktree).
# Usage: make_exp.py <goroot>
import os, re, sys

R = sys.argv[1]
AES = os.path.join(R, "src/crypto/internal/fips140/aes")

# index, name, width, evex, states, fold, feature
V = [
    (1, "ctrBulkXmm8f", 1, False, 8, True, "aes"),
    (2, "ctrBulkXmm8", 1, False, 8, False, "aes"),
    (3, "ctrBulkYmm4f", 2, False, 4, True, "vaes"),
    (4, "ctrBulkYmm6f", 2, False, 6, True, "vaes"),
    (5, "ctrBulkYmm8f", 2, False, 8, True, "vaes"),
    (6, "ctrBulkYmm8", 2, False, 8, False, "vaes"),
    (7, "ctrBulkZmm4f", 4, True, 4, True, "avx512vaes"),
    (8, "ctrBulkZmm6f", 4, True, 6, True, "avx512vaes"),
    (9, "ctrBulkZmm8f", 4, True, 8, True, "avx512vaes"),
    (10, "ctrBulkZmm4", 4, True, 4, False, "avx512vaes"),
    (11, "ctrBulkEy8f", 2, True, 8, True, "avx512vaes"),
    (12, "ctrBulkEy4f", 2, True, 4, True, "avx512vaes"),
]

def write(path, text):
    with open(path, "w") as f:
        f.write(text)

# 1. Generator main(): emit the variants after the fixed-size functions.
p = os.path.join(AES, "_asm/ctr/ctr_amd64_asm.go")
t = open(p).read()
calls = "".join("\tgenBulk(bulkVariant{name: %r, width: %d, evex: %s, states: %d, fold: %s})\n"
                % (n, w, str(e).lower(), s, str(f).lower()) for _, n, w, e, s, f, _ in V).replace("'", '"')
old = "\tctrBlocks(8)\n\n\tGenerate()\n"
assert t.count(old) == 1, "main"
write(p, t.replace(old, "\tctrBlocks(8)\n\n" + calls + "\n\tGenerate()\n"))

# 2. Declarations, variant selection and the bulk predicate.
decls = "".join("//go:noescape\nfunc %s(nr int, xk *[60]uint32, dst, src *byte, n int, ivlo, ivhi uint64)\n\n" % n
                for _, n, *_ in V)
feat = {"aes": "supportsAES", "vaes": "supportsAES && cpu.X86HasVAES && cpu.X86HasAVX2",
        "avx512vaes": "supportsAES && cpu.X86HasAVX512VAES"}
cases = "".join("\tcase %d:\n\t\treturn %s\n" % (i, feat[fe]) for i, _, _, _, _, _, fe in V)
names = ", ".join('%d: "%s"' % (i, n) for i, n, *_ in V)
write(os.path.join(AES, "ctr_amd64.go"), """// Experiment only.

//go:build !purego

package aes

import "crypto/internal/fips140deps/cpu"

// ctrVariant selects the bulk function; 0 is master's loop.
var ctrVariant = 0

// CTRVariants maps the experiment's variants to their names.
var CTRVariants = map[int]string{%s}

// SetCTRVariant selects a variant; it reports whether the CPU supports it.
func SetCTRVariant(v int) bool {
	if v != 0 && !ctrVariantSupported(v) {
		return false
	}
	ctrVariant = v
	return true
}

func ctrVariantSupported(v int) bool {
	switch v {
%s\t}
	return false
}

func ctrBulk(n, ivlo uint64) bool {
	return ctrVariant != 0 && n > 0 && n-1 <= ^ivlo
}

const supportsAESEOR3 = false

%s""" % (names, cases, decls))

# 3. ctr.go: a switch on the variant instead of the arm64 EOR3 choice.
p = os.path.join(AES, "ctr.go")
t = open(p).read()
old = """\t\tif supportsAESEOR3 {
\t\t\tctrBlocksBulkEOR3(&c.b, &dst[0], &src[0], n, ivlo, ivhi)
\t\t} else {
\t\t\tctrBlocksBulk(&c.b, &dst[0], &src[0], n, ivlo, ivhi)
\t\t}
"""
sw = "\t\tswitch ctrVariant {\n" + "".join(
    "\t\tcase %d:\n\t\t\t%s(c.b.rounds, &c.b.enc, &dst[0], &src[0], int(n), ivlo, ivhi)\n" % (i, n)
    for i, n, *_ in V) + "\t\t}\n"
assert t.count(old) == 1, "ctr.go"
write(p, t.replace(old, sw))

# 4. ctr_nobulk.go: not on amd64 any more.
p = os.path.join(AES, "ctr_nobulk.go")
t = open(p).read()
assert t.count("//go:build !arm64 || purego") == 1
write(p, t.replace("//go:build !arm64 || purego", "//go:build (!arm64 && !amd64) || purego"))

# 5. fips140deps/cpu: the VAES flags.
p = os.path.join(R, "src/crypto/internal/fips140deps/cpu/cpu.go")
t = open(p).read()
old = "\tX86HasAVX2      = cpu.X86.HasAVX2\n"
assert t.count(old) == 1
t = t.replace(old, old + "\tX86HasAVX512VAES = cpu.X86.HasAVX512VAES\n")
old = "\tX86HasSSSE3     = cpu.X86.HasSSSE3\n"
assert t.count(old) == 1
write(p, t.replace(old, old + "\tX86HasVAES      = cpu.X86.HasVAES\n"))

# 6. Correctness test of every variant the CPU supports.
write(os.path.join(AES, "ctr_amd64_test.go"), """// Experiment only.

//go:build !purego

package aes

import (
	"bytes"
	"crypto/internal/fips140deps/byteorder"
	"testing"
)

func ctrReferenceAmd64(key, src []byte, ivlo, ivhi uint64) []byte {
	defer func(v bool) { supportsAES = v }(supportsAES)
	supportsAES = false
	var c blockExpanded
	c.rounds = map[int]int{16: aes128Rounds, 24: aes192Rounds, 32: aes256Rounds}[len(key)]
	expandKeyGeneric(&c, key)
	out := make([]byte, len(src))
	var ctr, ks [BlockSize]byte
	for i := 0; i < len(src); i += BlockSize {
		byteorder.BEPutUint64(ctr[:8], ivhi)
		byteorder.BEPutUint64(ctr[8:], ivlo)
		encryptBlockGeneric(&c, ks[:], ctr[:])
		for j := range BlockSize {
			out[i+j] = src[i+j] ^ ks[j]
		}
		ivlo, ivhi = add128(ivlo, ivhi, 1)
	}
	return out
}

func TestCTRBulkVariants(t *testing.T) {
	defer func(v int) { ctrVariant = v }(ctrVariant)
	key := make([]byte, 32)
	for i := range key {
		key[i] = byte(i*7 + 1)
	}
	for v := 1; v <= len(CTRVariants); v++ {
		if !SetCTRVariant(v) {
			t.Logf("%s: not supported here", CTRVariants[v])
			continue
		}
		for _, keySize := range []int{16, 24, 32} {
			var b Block
			newBlock(&b, key[:keySize])
			for _, ivhi := range []uint64{0, ^uint64(0)} {
				for _, ivlo := range []uint64{0, 1 << 63, ^uint64(0) - 200, ^uint64(0) - 70, ^uint64(0) - 33, ^uint64(0)} {
					var iv [BlockSize]byte
					byteorder.BEPutUint64(iv[:8], ivhi)
					byteorder.BEPutUint64(iv[8:], ivlo)
					c := NewCTR(&b, iv[:])
					for n := 1; n <= 100; n++ {
						src := make([]byte, n*BlockSize+7)
						for i := range src {
							src[i] = byte(i*131 + n)
						}
						want := ctrReferenceAmd64(key[:keySize], src[:n*BlockSize], ivlo, ivhi)
						got := make([]byte, len(src))
						c.XORKeyStreamAt(got, src, 0)
						if !bytes.Equal(got[:n*BlockSize], want) {
							t.Fatalf("%s key=%d ivhi=%#x ivlo=%#x n=%d: wrong output", CTRVariants[v], keySize, ivhi, ivlo, n)
						}
						c.XORKeyStreamAt(src, src, 0)
						if !bytes.Equal(src[:n*BlockSize], want) {
							t.Fatalf("%s key=%d ivhi=%#x ivlo=%#x n=%d: wrong output in place", CTRVariants[v], keySize, ivhi, ivlo, n)
						}
					}
				}
			}
		}
	}
}
""")

# 7. crypto/cipher: select the variant from $CTRV for the benchmarks.
write(os.path.join(R, "src/crypto/cipher/ctr_exp_test.go"), """// Experiment only.

package cipher_test

import (
	"crypto/internal/fips140/aes"
	"fmt"
	"os"
	"strconv"
)

func init() {
	s := os.Getenv("CTRV")
	if s == "" {
		return
	}
	v, err := strconv.Atoi(s)
	if err != nil || !aes.SetCTRVariant(v) {
		fmt.Fprintf(os.Stderr, "CTRV=%s: unsupported variant\\n", s)
		os.Exit(3)
	}
}
""")
print("variants:", len(V))
