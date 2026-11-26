// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import (
	"fmt"
	"sync"

	. "github.com/mmcloughlin/avo/build"
	. "github.com/mmcloughlin/avo/operand"
	. "github.com/mmcloughlin/avo/reg"
)

// bulkVariant describes one bulk CTR function:
//
//	func name(nr int, xk *[60]uint32, dst, src *byte, n int, ivlo, ivhi uint64)
//
// which XORs n >= 1 blocks of keystream into dst, starting at counter
// ivhi*2^64 + ivlo. The caller guarantees that the low 64 bits of the counter
// do not wrap within the n blocks, and that dst and src are the same buffer or
// do not overlap.
type bulkVariant struct {
	name   string
	width  int  // blocks per vector register: 1 (XMM, legacy SSE), 2 (YMM), 4 (ZMM)
	evex   bool // AVX-512 encodings: 32 registers, so the round keys stay in registers
	states int  // vector registers per loop iteration
	fold   bool // XOR the source into the last round key: AESENCLAST(state, key ^ src)
}

var (
	xRegs = []VecPhysical{X0, X1, X2, X3, X4, X5, X6, X7, X8, X9, X10, X11, X12, X13, X14, X15,
		X16, X17, X18, X19, X20, X21, X22, X23, X24, X25, X26, X27, X28, X29, X30, X31}
	yRegs = []VecPhysical{Y0, Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10, Y11, Y12, Y13, Y14, Y15,
		Y16, Y17, Y18, Y19, Y20, Y21, Y22, Y23, Y24, Y25, Y26, Y27, Y28, Y29, Y30, Y31}
	zRegs = []VecPhysical{Z0, Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15,
		Z16, Z17, Z18, Z19, Z20, Z21, Z22, Z23, Z24, Z25, Z26, Z27, Z28, Z29, Z30, Z31}
)

// vec returns register i at a width of w blocks.
func vec(w, i int) VecPhysical {
	switch w {
	case 1:
		return xRegs[i]
	case 2:
		return yRegs[i]
	}
	return zRegs[i]
}

// Register roles. States use 0..7.
const (
	regKey   = 8  // round key (keys from memory) or a temporary
	regCtr   = 9  // counter: [lo, hi] little-endian in every 128-bit lane
	regMask  = 10 // byte reversal within each 128-bit lane
	regInc   = 11 // [G, 0] in every lane: the counter step of one loop iteration
	regTmp   = 12 // source XOR last key, or source
	regTmp2  = 13 // counter step of a tail group
	regKey0  = 15 // EVEX: round key 0
	regKeyHi = 30 // EVEX: the last round key; key i of nr is in register 30-nr+i (i >= 1)
)

// ctrOffsets holds the 128-bit little-endian values 0, 1, ..., 32.
var ctrOffsets = sync.OnceValue(func() Mem {
	m := GLOBL("ctrOffsets", NOPTR|RODATA)
	for k := 0; k <= 32; k++ {
		DATA(16*k, U64(uint64(k)))
		DATA(16*k+8, U64(0))
	}
	return m
})

type bulkGen struct {
	v                       bulkVariant
	nr, xk, kp, dst, src, n GPPhysical
	labels                  int
}

func (g *bulkGen) label(s string) string {
	g.labels++
	return fmt.Sprintf("%s_%s%d", g.v.name, s, g.labels)
}

func genBulk(v bulkVariant) {
	Implement(v.name)
	g := &bulkGen{v: v}

	// Physical general-purpose registers keep the code readable and stable.
	g.nr, g.xk, g.kp, g.dst, g.src, g.n = RAX, RBX, RCX, RDX, RSI, RDI
	ivlo, ivhi := R8, R9
	Load(Param("nr"), g.nr)
	Load(Param("xk"), g.xk)
	Load(Param("dst"), g.dst)
	Load(Param("src"), g.src)
	Load(Param("n"), g.n)
	Load(Param("ivlo"), ivlo)
	Load(Param("ivhi"), ivhi)

	// kp = xk + 16*(nr-10): the last ten round keys are at kp+16 ... kp+160
	// for every key size, so the rounds can share code (see rounds).
	MOVQ(g.nr, g.kp)
	SHLQ(Imm(4), g.kp)
	ADDQ(g.xk, g.kp)
	SUBQ(U32(160), g.kp)

	w := v.width
	G := v.states * w
	c := vec(w, regCtr)
	if w == 1 {
		MOVQ(ivlo, c)
		PINSRQ(Imm(1), ivhi, c)
		MOVOU(bswapMask(), vec(1, regMask))
		MOVOU(ctrOffsets().Offset(16*G), vec(1, regInc))
	} else {
		xc := vec(1, regCtr)
		VMOVQ(ivlo, xc)
		VPINSRQ(Imm(1), ivhi, xc, xc)
		if w == 2 {
			VINSERTI128(Imm(1), xc, c, c)
			VBROADCASTI128(bswapMask(), vec(2, regMask))
			VBROADCASTI128(ctrOffsets().Offset(16*G), vec(2, regInc))
		} else {
			VSHUFI64X2(Imm(0), c, c, c)
			VBROADCASTI32X4(bswapMask(), vec(4, regMask))
			VBROADCASTI32X4(ctrOffsets().Offset(16*G), vec(4, regInc))
		}
	}
	if v.evex {
		g.loadKeys()
	}

	loop, tail := g.label("loop"), g.label("tail")
	CMPQ(g.n, U32(G))
	JB(LabelRef(tail))
	Label(loop)
	g.group(v.states, w)
	g.addCtr(w, vec(w, regInc))
	SUBQ(U32(G), g.n)
	CMPQ(g.n, U32(G))
	JAE(LabelRef(loop))

	// The tail: n < G blocks, in groups of 4, 2 and 1 vectors, then of
	// narrower vectors.
	Label(tail)
	for k := 4; k >= 1; k /= 2 {
		if k >= v.states {
			continue
		}
		g.tailGroup(k, w)
	}
	for ww := w / 2; ww >= 1; ww /= 2 {
		g.tailGroup(1, ww)
	}
	if w > 1 {
		VZEROUPPER()
	}
	RET()
}

// tailGroup encrypts k vectors of ww blocks if bit k*ww of n is set.
func (g *bulkGen) tailGroup(k, ww int) {
	skip := g.label("skip")
	TESTQ(U32(k*ww), g.n)
	JZ(LabelRef(skip))
	g.group(k, ww)
	// Advance the counter by k*ww blocks.
	step := vec(g.v.width, regTmp2)
	switch g.v.width {
	case 1:
		MOVOU(ctrOffsets().Offset(16*k*ww), step)
	case 2:
		VBROADCASTI128(ctrOffsets().Offset(16*k*ww), step)
	default:
		VBROADCASTI32X4(ctrOffsets().Offset(16*k*ww), step)
	}
	g.addCtr(g.v.width, step)
	Label(skip)
}

// addCtr adds step to the counter register at the variant's full width.
func (g *bulkGen) addCtr(w int, step VecPhysical) {
	c := vec(w, regCtr)
	if w == 1 {
		PADDQ(step, c)
	} else {
		VPADDQ(step, c, c)
	}
}

// loadKeys broadcasts the round keys into registers (EVEX variants): key 0
// into register 15 and key i of nr into register 30-nr+i.
func (g *bulkGen) loadKeys() {
	w := g.v.width
	bcast := func(m Mem, r int) { VBROADCASTI32X4(m, vec(w, r)) }
	bcast(Mem{Base: g.xk}, regKey0)
	l192, l128 := g.label("keys192"), g.label("keys128")
	CMPQ(g.nr, Imm(12))
	JB(LabelRef(l128))
	JE(LabelRef(l192))
	bcast(Mem{Base: g.kp, Disp: -48}, regKeyHi-13)
	bcast(Mem{Base: g.kp, Disp: -32}, regKeyHi-12)
	Label(l192)
	bcast(Mem{Base: g.kp, Disp: -16}, regKeyHi-11)
	bcast(Mem{Base: g.kp, Disp: 0}, regKeyHi-10)
	Label(l128)
	for i := 1; i <= 10; i++ {
		bcast(Mem{Base: g.kp, Disp: 16 * i}, regKeyHi-10+i)
	}
}

// group encrypts k vectors of ww blocks: counters, rounds, and the XOR into
// dst; then advances src and dst.
func (g *bulkGen) group(k, ww int) {
	v := g.v
	st := func(j int) VecPhysical { return vec(ww, j) }

	// Counters: state j, lane l is the counter plus j*ww + l, byte-reversed.
	if v.width == 1 {
		c := vec(1, regCtr)
		one := vec(1, regTmp2)
		MOVOU(ctrOffsets().Offset(16), one)
		for j := 0; j < k; j++ {
			if j == 0 {
				MOVO(c, st(0))
			} else {
				MOVO(st(j-1), st(j))
				PADDQ(one, st(j))
			}
		}
		for j := 0; j < k; j++ {
			PSHUFB(vec(1, regMask), st(j))
		}
	} else {
		for j := 0; j < k; j++ {
			VPADDQ(ctrOffsets().Offset(16*j*ww), vec(ww, regCtr), st(j))
			VPSHUFB(vec(ww, regMask), st(j), st(j))
		}
	}

	// Round 0: XOR with key 0.
	if v.evex {
		for j := 0; j < k; j++ {
			VPXORD(vec(ww, regKey0), st(j), st(j))
		}
	} else {
		g.loadKey(ww, Mem{Base: g.xk})
		for j := 0; j < k; j++ {
			if v.width == 1 {
				PXOR(vec(1, regKey), st(j))
			} else {
				VPXOR(vec(ww, regKey), st(j), st(j))
			}
		}
	}

	// Rounds 1 to nr-1, sharing code between key sizes: AES-256 starts at
	// the key at kp-48, AES-192 at kp-16, AES-128 at kp+16.
	l192, l128 := g.label("r192"), g.label("r128")
	CMPQ(g.nr, Imm(12))
	JB(LabelRef(l128))
	JE(LabelRef(l192))
	g.aesRound(k, ww, -48, regKeyHi-13)
	g.aesRound(k, ww, -32, regKeyHi-12)
	Label(l192)
	g.aesRound(k, ww, -16, regKeyHi-11)
	g.aesRound(k, ww, 0, regKeyHi-10)
	Label(l128)
	for i := 1; i <= 9; i++ {
		g.aesRound(k, ww, 16*i, regKeyHi-10+i)
	}

	// The last round and the XOR with src.
	var last VecPhysical
	if v.evex {
		last = vec(ww, regKeyHi)
	} else {
		g.loadKey(ww, Mem{Base: g.kp, Disp: 160})
		last = vec(ww, regKey)
	}
	t := vec(ww, regTmp)
	for j := 0; j < k; j++ {
		s := Mem{Base: g.src, Disp: 16 * ww * j}
		d := Mem{Base: g.dst, Disp: 16 * ww * j}
		switch {
		case v.width == 1 && v.fold:
			MOVOU(s, t)
			PXOR(last, t)
			AESENCLAST(t, st(j))
			MOVOU(st(j), d)
		case v.width == 1:
			AESENCLAST(last, st(j))
			MOVOU(s, t)
			PXOR(st(j), t)
			MOVOU(t, d)
		case v.fold:
			if v.evex {
				VPXORD(s, last, t)
			} else {
				VPXOR(s, last, t)
			}
			VAESENCLAST(t, st(j), st(j))
			g.store(ww, st(j), d)
		default:
			VAESENCLAST(last, st(j), st(j))
			if v.evex {
				VPXORD(s, st(j), st(j))
			} else {
				VPXOR(s, st(j), st(j))
			}
			g.store(ww, st(j), d)
		}
	}
	ADDQ(U32(16*ww*k), g.src)
	ADDQ(U32(16*ww*k), g.dst)
}

func (g *bulkGen) store(ww int, r VecPhysical, d Mem) {
	if g.v.evex {
		VMOVDQU64(r, d)
	} else {
		VMOVDQU(r, d)
	}
}

// loadKey loads the round key at m into the key register (keys from memory).
func (g *bulkGen) loadKey(ww int, m Mem) {
	switch {
	case ww == 1 && g.v.width == 1:
		MOVOU(m, vec(1, regKey))
	case ww == 1:
		VMOVDQU(m, vec(1, regKey))
	default:
		VBROADCASTI128(m, vec(2, regKey))
	}
}

// aesRound runs one AESENC round with the key at kp+disp (keys from memory)
// or in register r (EVEX).
func (g *bulkGen) aesRound(k, ww, disp, r int) {
	var key VecPhysical
	if g.v.evex {
		key = vec(ww, r)
	} else {
		g.loadKey(ww, Mem{Base: g.kp, Disp: disp})
		key = vec(ww, regKey)
	}
	for j := 0; j < k; j++ {
		if g.v.width == 1 {
			AESENC(key, vec(1, j))
		} else {
			VAESENC(key, vec(ww, j), vec(ww, j))
		}
	}
}
