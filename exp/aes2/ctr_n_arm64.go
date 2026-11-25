// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build !purego

package aes

// ctrBlocksLoopAsm XORs n groups of ctrGroupBlocks blocks and then r more
// blocks (r == 0 unless ctrAsmTail) of keystream into dst. The low 64 bits of
// the counter must not wrap: ivlo + G*n + r <= 2^64. dst and src are equal or
// do not overlap.
//
//go:noescape
func ctrBlocksLoopAsm(nr int, xk *[60]uint32, dst, src *byte, n, r int, ivlo, ivhi uint64)

// ctrBlocksN XORs len(src)/BlockSize blocks of keystream into dst.
// len(src) is a positive multiple of BlockSize and len(dst) == len(src).
func ctrBlocksN(b *Block, dst, src []byte, ivlo, ivhi uint64) {
	if !supportsAES {
		ctrBlocksNGeneric(b, dst, src, ivlo, ivhi)
		return
	}
	const G = ctrGroupBlocks
	for len(src) > 0 {
		k := uint64(len(src)) / BlockSize
		// Blocks before the low 64 bits of the counter wrap: 2^64 - ivlo.
		if ivlo != 0 && -ivlo < k {
			k = -ivlo
		}
		n, r := k/G, k%G
		if ctrAsmTail {
			ctrBlocksLoopAsm(b.rounds, &b.enc, &dst[0], &src[0], int(n), int(r), ivlo, ivhi)
		} else {
			if n > 0 {
				ctrBlocksLoopAsm(b.rounds, &b.enc, &dst[0], &src[0], int(n), 0, ivlo, ivhi)
			}
			off := n * G * BlockSize
			lo, hi := add128(ivlo, ivhi, n*G)
			d, s := dst[off:k*BlockSize], src[off:k*BlockSize]
			if r >= 8 {
				ctrBlocks8Asm(b.rounds, &b.enc, (*[8 * BlockSize]byte)(d), (*[8 * BlockSize]byte)(s), lo, hi)
				lo, hi = add128(lo, hi, 8)
				d, s = d[8*BlockSize:], s[8*BlockSize:]
			}
			if r&4 != 0 {
				ctrBlocks4Asm(b.rounds, &b.enc, (*[4 * BlockSize]byte)(d), (*[4 * BlockSize]byte)(s), lo, hi)
				lo, hi = add128(lo, hi, 4)
				d, s = d[4*BlockSize:], s[4*BlockSize:]
			}
			if r&2 != 0 {
				ctrBlocks2Asm(b.rounds, &b.enc, (*[2 * BlockSize]byte)(d), (*[2 * BlockSize]byte)(s), lo, hi)
				lo, hi = add128(lo, hi, 2)
				d, s = d[2*BlockSize:], s[2*BlockSize:]
			}
			if r&1 != 0 {
				ctrBlocks1Asm(b.rounds, &b.enc, (*[BlockSize]byte)(d), (*[BlockSize]byte)(s), lo, hi)
			}
		}
		ivlo, ivhi = add128(ivlo, ivhi, k)
		dst, src = dst[k*BlockSize:], src[k*BlockSize:]
	}
}
