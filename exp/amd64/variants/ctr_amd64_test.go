// Experiment only.

//go:build !purego

package aes

import (
	"bytes"
	"crypto/internal/fips140deps/byteorder"
	"testing"
)

func ctrReferenceAmd64(key, src []byte, ivlo, ivhi uint64) []byte {
	defer func(v bool) { supportsAES = v }(supportsAES)
	supportsAES = false
	var c blockExpanded
	c.rounds = map[int]int{16: aes128Rounds, 24: aes192Rounds, 32: aes256Rounds}[len(key)]
	expandKeyGeneric(&c, key)
	out := make([]byte, len(src))
	var ctr, ks [BlockSize]byte
	for i := 0; i < len(src); i += BlockSize {
		byteorder.BEPutUint64(ctr[:8], ivhi)
		byteorder.BEPutUint64(ctr[8:], ivlo)
		encryptBlockGeneric(&c, ks[:], ctr[:])
		for j := range BlockSize {
			out[i+j] = src[i+j] ^ ks[j]
		}
		ivlo, ivhi = add128(ivlo, ivhi, 1)
	}
	return out
}

func TestCTRBulkVariants(t *testing.T) {
	defer func(v int) { ctrVariant = v }(ctrVariant)
	key := make([]byte, 32)
	for i := range key {
		key[i] = byte(i*7 + 1)
	}
	for v := 1; v <= len(CTRVariants); v++ {
		if !SetCTRVariant(v) {
			t.Logf("%s: not supported here", CTRVariants[v])
			continue
		}
		for _, keySize := range []int{16, 24, 32} {
			var b Block
			newBlock(&b, key[:keySize])
			for _, ivhi := range []uint64{0, ^uint64(0)} {
				for _, ivlo := range []uint64{0, 1 << 63, ^uint64(0) - 200, ^uint64(0) - 70, ^uint64(0) - 33, ^uint64(0)} {
					var iv [BlockSize]byte
					byteorder.BEPutUint64(iv[:8], ivhi)
					byteorder.BEPutUint64(iv[8:], ivlo)
					c := NewCTR(&b, iv[:])
					for n := 1; n <= 100; n++ {
						src := make([]byte, n*BlockSize+7)
						for i := range src {
							src[i] = byte(i*131 + n)
						}
						want := ctrReferenceAmd64(key[:keySize], src[:n*BlockSize], ivlo, ivhi)
						got := make([]byte, len(src))
						c.XORKeyStreamAt(got, src, 0)
						if !bytes.Equal(got[:n*BlockSize], want) {
							t.Fatalf("%s key=%d ivhi=%#x ivlo=%#x n=%d: wrong output", CTRVariants[v], keySize, ivhi, ivlo, n)
						}
						c.XORKeyStreamAt(src, src, 0)
						if !bytes.Equal(src[:n*BlockSize], want) {
							t.Fatalf("%s key=%d ivhi=%#x ivlo=%#x n=%d: wrong output in place", CTRVariants[v], keySize, ivhi, ivlo, n)
						}
					}
				}
			}
		}
	}
}
