// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build !purego

package aes

import "crypto/internal/fips140deps/cpu"

const ctrBulk = true

// ctrSmall: full-block counts below it use the fixed-size helpers (experiment knob).
const ctrSmall = SMALLVAL

var supportsAESEOR3 = supportsAES && cpu.ARM64HasSHA3

//go:noescape
func ctrBlocksAsm(nr int, xk *[60]uint32, dst, src *byte, n, r int, ivlo, ivhi uint64)

//go:noescape
func ctrBlocksEOR3Asm(nr int, xk *[60]uint32, dst, src *byte, n, r int, ivlo, ivhi uint64)

// ctrBlocksN XORs n >= 1 blocks of keystream into dst, from counter ivhi*2^64 + ivlo.
// len(dst) and len(src) are at least n*BlockSize.
func ctrBlocksN(b *Block, dst, src []byte, n, ivlo, ivhi uint64) {
	if n < ctrSmall {
		ctrBlocksSmall(b, dst, src, n, ivlo, ivhi)
		return
	}
	if !supportsAES || n-1 > ^ivlo {
		ctrBlocksNSlow(b, dst, src, n, ivlo, ivhi)
		return
	}
	ctrBlocksNAsm(b, &dst[0], &src[0], n, ivlo, ivhi)
}

func ctrBlocksSmall(b *Block, dst, src []byte, n, ivlo, ivhi uint64) {
	if n >= 4 {
		ctrBlocks4(b, (*[4 * BlockSize]byte)(dst), (*[4 * BlockSize]byte)(src), ivlo, ivhi)
		dst, src = dst[4*BlockSize:], src[4*BlockSize:]
		ivlo, ivhi = add128(ivlo, ivhi, 4)
	}
	if n&2 != 0 {
		ctrBlocks2(b, (*[2 * BlockSize]byte)(dst), (*[2 * BlockSize]byte)(src), ivlo, ivhi)
		dst, src = dst[2*BlockSize:], src[2*BlockSize:]
		ivlo, ivhi = add128(ivlo, ivhi, 2)
	}
	if n&1 != 0 {
		ctrBlocks1(b, (*[BlockSize]byte)(dst), (*[BlockSize]byte)(src), ivlo, ivhi)
	}
}

func ctrBlocksNAsm(b *Block, dst, src *byte, n, ivlo, ivhi uint64) {
	if supportsAESEOR3 {
		ctrBlocksEOR3Asm(b.rounds, &b.enc, dst, src, int(n/12), int(n%12), ivlo, ivhi)
	} else {
		ctrBlocksAsm(b.rounds, &b.enc, dst, src, int(n/12), int(n%12), ivlo, ivhi)
	}
}

// ctrBlocksNSlow handles the cases ctrBlocksN does not: no AES instructions,
// or a counter whose low 64 bits wrap within the n blocks.
func ctrBlocksNSlow(b *Block, dst, src []byte, n, ivlo, ivhi uint64) {
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
	k := -ivlo // blocks before the low 64 bits wrap; 0 < k < n
	ctrBlocksNAsm(b, &dst[0], &src[0], k, ivlo, ivhi)
	ivlo, ivhi = add128(ivlo, ivhi, k)
	ctrBlocksNAsm(b, &dst[k*BlockSize], &src[k*BlockSize], n-k, ivlo, ivhi)
}
