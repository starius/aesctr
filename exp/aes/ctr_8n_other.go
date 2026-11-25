// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build !arm64 || purego

package aes

// ctrBlocks8N XORs len(src)/BlockSize blocks of keystream into dst.
// len(src) is a positive multiple of 8*BlockSize and len(dst) == len(src).
func ctrBlocks8N(b *Block, dst, src []byte, ivlo, ivhi uint64) {
	for len(src) > 0 {
		ctrBlocks8(b, (*[8 * BlockSize]byte)(dst), (*[8 * BlockSize]byte)(src), ivlo, ivhi)
		src, dst = src[8*BlockSize:], dst[8*BlockSize:]
		ivlo, ivhi = add128(ivlo, ivhi, 8)
	}
}
