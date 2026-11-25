// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build !purego

package aes

import "crypto/internal/fips140deps/cpu"

// ctrBulk reports whether xorKeyStreamAt passes all full blocks to ctrBlocksBulk.
const ctrBulk = true

// supportsAESEOR3 selects ctrBlocksBulkEOR3Asm, which needs FEAT_SHA3.
var supportsAESEOR3 = supportsAES && cpu.ARM64HasSHA3

// ctrBlocksBulkAsm and ctrBlocksBulkEOR3Asm XOR n >= 0 groups of 12 blocks and
// then 0 <= r < 12 more blocks of keystream into dst, starting at counter
// ivhi*2^64 + ivlo.
// The low 64 bits of the counter must not wrap: ivlo + 12*n + r <= 2^64.
// dst and src must be the same buffer or not overlap.
//
//go:noescape
func ctrBlocksBulkAsm(nr int, xk *[60]uint32, dst, src *byte, n, r int, ivlo, ivhi uint64)

//go:noescape
func ctrBlocksBulkEOR3Asm(nr int, xk *[60]uint32, dst, src *byte, n, r int, ivlo, ivhi uint64)

// ctrBlocksBulk XORs n >= 1 blocks of keystream into dst, starting at counter
// ivhi*2^64 + ivlo. dst and src hold at least n blocks and are the same buffer
// or do not overlap.
func ctrBlocksBulk(b *Block, dst, src []byte, n, ivlo, ivhi uint64) {
	if !supportsAES || n-1 > ^ivlo {
		ctrBlocksBulkSlow(b, dst, src, n, ivlo, ivhi)
		return
	}
	if supportsAESEOR3 {
		ctrBlocksBulkEOR3Asm(b.rounds, &b.enc, &dst[0], &src[0], int(n/12), int(n%12), ivlo, ivhi)
	} else {
		ctrBlocksBulkAsm(b.rounds, &b.enc, &dst[0], &src[0], int(n/12), int(n%12), ivlo, ivhi)
	}
}

// ctrBlocksBulkSlow handles what ctrBlocksBulk does not: no AES instructions,
// or a counter whose low 64 bits wrap within the n blocks.
func ctrBlocksBulkSlow(b *Block, dst, src []byte, n, ivlo, ivhi uint64) {
	if !supportsAES {
		dst, src = dst[:n*BlockSize], src[:n*BlockSize]
		for len(src) > 0 {
			m := min(len(src), 8*BlockSize)
			ctrBlocks(b, dst[:m], src[:m], ivlo, ivhi)
			ivlo, ivhi = add128(ivlo, ivhi, uint64(m/BlockSize))
			dst, src = dst[m:], src[m:]
		}
		return
	}
	// The low 64 bits wrap after k = 2^64 - ivlo blocks, 0 < k < n. Neither
	// part wraps: a slice cannot hold 2^64 more blocks.
	k := -ivlo
	ctrBlocksBulk(b, dst, src, k, ivlo, ivhi)
	ivlo, ivhi = add128(ivlo, ivhi, k)
	ctrBlocksBulk(b, dst[k*BlockSize:], src[k*BlockSize:], n-k, ivlo, ivhi)
}
