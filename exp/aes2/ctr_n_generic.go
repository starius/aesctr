// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package aes

// ctrBlocksNGeneric is ctrBlocksN in terms of the fixed-size helpers.
func ctrBlocksNGeneric(b *Block, dst, src []byte, ivlo, ivhi uint64) {
	for len(src) >= 8*BlockSize {
		ctrBlocks8(b, (*[8 * BlockSize]byte)(dst), (*[8 * BlockSize]byte)(src), ivlo, ivhi)
		src, dst = src[8*BlockSize:], dst[8*BlockSize:]
		ivlo, ivhi = add128(ivlo, ivhi, 8)
	}
	if len(src) >= 4*BlockSize {
		ctrBlocks4(b, (*[4 * BlockSize]byte)(dst), (*[4 * BlockSize]byte)(src), ivlo, ivhi)
		src, dst = src[4*BlockSize:], dst[4*BlockSize:]
		ivlo, ivhi = add128(ivlo, ivhi, 4)
	}
	if len(src) >= 2*BlockSize {
		ctrBlocks2(b, (*[2 * BlockSize]byte)(dst), (*[2 * BlockSize]byte)(src), ivlo, ivhi)
		src, dst = src[2*BlockSize:], dst[2*BlockSize:]
		ivlo, ivhi = add128(ivlo, ivhi, 2)
	}
	if len(src) >= BlockSize {
		ctrBlocks1(b, (*[BlockSize]byte)(dst), (*[BlockSize]byte)(src), ivlo, ivhi)
	}
}
