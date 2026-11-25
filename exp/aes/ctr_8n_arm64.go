// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build !purego

package aes

// ctrBlocks8LoopAsm XORs n groups of ctrGroupBlocks blocks of keystream into
// dst. The low 64 bits of the counter must not wrap: ivlo + G*n <= 2^64.
//
//go:noescape
func ctrBlocks8LoopAsm(nr int, xk *[60]uint32, dst, src *byte, n int, ivlo, ivhi uint64)

// ctrBlocks8N XORs len(src)/BlockSize blocks of keystream into dst.
// len(src) is a positive multiple of 8*BlockSize and len(dst) == len(src).
func ctrBlocks8N(b *Block, dst, src []byte, ivlo, ivhi uint64) {
	if !supportsAES {
		for len(src) > 0 {
			ctrBlocks(b, dst[:8*BlockSize], src[:8*BlockSize], ivlo, ivhi)
			src, dst = src[8*BlockSize:], dst[8*BlockSize:]
			ivlo, ivhi = add128(ivlo, ivhi, 8)
		}
		return
	}
	const G = ctrGroupBlocks
	for len(src) >= G*BlockSize {
		n := uint64(len(src)) / (G * BlockSize)
		// Groups that end before the low 64 bits of the counter wrap.
		if ivlo != 0 && -ivlo/G < n {
			n = -ivlo / G
		}
		if n == 0 {
			// The next group crosses the wrap; the 4-block function carries.
			ctrBlocks4Asm(b.rounds, &b.enc, (*[4 * BlockSize]byte)(dst), (*[4 * BlockSize]byte)(src), ivlo, ivhi)
			ivlo, ivhi = add128(ivlo, ivhi, 4)
			dst, src = dst[4*BlockSize:], src[4*BlockSize:]
			continue
		}
		ctrBlocks8LoopAsm(b.rounds, &b.enc, &dst[0], &src[0], int(n), ivlo, ivhi)
		ivlo, ivhi = add128(ivlo, ivhi, G*n)
		dst, src = dst[n*G*BlockSize:], src[n*G*BlockSize:]
	}
	for len(src) > 0 {
		ctrBlocks4Asm(b.rounds, &b.enc, (*[4 * BlockSize]byte)(dst), (*[4 * BlockSize]byte)(src), ivlo, ivhi)
		ivlo, ivhi = add128(ivlo, ivhi, 4)
		dst, src = dst[4*BlockSize:], src[4*BlockSize:]
	}
}
