// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

//go:build !arm64 || purego

package aes

const ctrBulk = false

func ctrBlocksN(b *Block, dst, src []byte, n, ivlo, ivhi uint64) {
	panic("unreachable")
}
