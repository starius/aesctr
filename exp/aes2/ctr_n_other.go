// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build !arm64 || purego

package aes

// ctrBlocksN XORs len(src)/BlockSize blocks of keystream into dst.
func ctrBlocksN(b *Block, dst, src []byte, ivlo, ivhi uint64) {
	ctrBlocksNGeneric(b, dst, src, ivlo, ivhi)
}
