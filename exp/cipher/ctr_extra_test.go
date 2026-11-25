// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package cipher_test

import (
	"bytes"
	"crypto/aes"
	"crypto/cipher"
	"encoding/binary"
	"fmt"
	"math/rand"
	"testing"
)

// TestCTRExtraWrap checks lengths 0..70 blocks (plus a partial block) around a
// wrap of the low 64 counter bits at every position, for all key sizes, both
// in place and into a separate buffer, against the generic implementation.
func TestCTRExtraWrap(t *testing.T) {
	r := rand.New(rand.NewSource(1))
	for _, keySize := range []int{16, 24, 32} {
		key := make([]byte, keySize)
		r.Read(key)
		block, err := aes.NewCipher(key)
		if err != nil {
			t.Fatal(err)
		}
		for _, hi := range []uint64{0, 7, ^uint64(0)} {
			for k := 1; k <= 40; k++ {
				var iv [16]byte
				binary.BigEndian.PutUint64(iv[:8], hi)
				binary.BigEndian.PutUint64(iv[8:], -uint64(k))
				for _, nblocks := range []int{0, 1, 2, 3, 7, 8, 9, 11, 12, 13, 15, 16, 23, 24, 25, 31, 47, 48, 70} {
					for _, extra := range []int{0, 5} {
						n := nblocks*16 + extra
						src := make([]byte, n)
						r.Read(src)
						generic, multiblock := makeTestingCiphers(block, iv[:])
						want := make([]byte, n)
						generic.XORKeyStream(want, src)
						got := make([]byte, n)
						multiblock.XORKeyStream(got, src)
						if !bytes.Equal(got, want) {
							t.Fatalf("key %d hi %x k %d n %d: mismatch", keySize, hi, k, n)
						}
						_, multiblock = makeTestingCiphers(block, iv[:])
						inplace := bytes.Clone(src)
						multiblock.XORKeyStream(inplace, inplace)
						if !bytes.Equal(inplace, want) {
							t.Fatalf("key %d hi %x k %d n %d: in-place mismatch", keySize, hi, k, n)
						}
					}
				}
			}
		}
	}
}

func BenchmarkCTRExtra(b *testing.B) {
	for _, keySize := range []int{16, 32} {
		for _, n := range []int{16, 64, 128, 192, 384, 4096, 65536} {
			b.Run(fmt.Sprintf("%d/%d", keySize*8, n), func(b *testing.B) {
				block, _ := aes.NewCipher(make([]byte, keySize))
				stream := cipher.NewCTR(block, make([]byte, 16))
				buf := make([]byte, n)
				b.SetBytes(int64(n))
				for i := 0; i < b.N; i++ {
					stream.XORKeyStream(buf, buf)
				}
			})
		}
	}
}

func BenchmarkCTRSmall(b *testing.B) {
	for _, keySize := range []int{16, 32} {
		sizes := []int{16, 32, 48, 64, 80, 96, 112, 128, 144, 192, 4096}
		if keySize == 32 {
			sizes = []int{16, 64, 128, 4096}
		}
		for _, n := range sizes {
			b.Run(fmt.Sprintf("%d/%d", keySize*8, n), func(b *testing.B) {
				block, _ := aes.NewCipher(make([]byte, keySize))
				stream := cipher.NewCTR(block, make([]byte, 16))
				buf := make([]byte, n)
				b.SetBytes(int64(n))
				for i := 0; i < b.N; i++ {
					stream.XORKeyStream(buf, buf)
				}
			})
		}
	}
}
