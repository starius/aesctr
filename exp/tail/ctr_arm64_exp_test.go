// Experiment only: correctness and direct-call benchmarks of the tail variants.

//go:build !purego

package aes

import (
	"bytes"
	"crypto/internal/fips140deps/cpu"
	"fmt"
	"testing"
	"unsafe"
)

type bulkFunc func(nr int, xk *[60]uint32, dst, src *byte, n, r int, ivlo, ivhi uint64)

var expVariants = []struct {
	name string
	eor3 bool
	f    bulkFunc
}{
	{"cl", false, ctrBlocksBulkAsm},
	{"clE3", true, ctrBlocksBulkEOR3Asm},
	{"pairs", false, ctrBulkPairs},
	{"ld4", false, ctrBulkLd4},
	{"pre", false, ctrBulkPre},
	{"align", false, ctrBulkAlign},
	{"e3pairs", true, ctrBulkE3Pairs},
	{"e3ld4", true, ctrBulkE3Ld4},
	{"e3pre", true, ctrBulkE3Pre},
}

func TestExpVariants(t *testing.T) {
	if !supportsAES {
		t.Skip("no AES instructions")
	}
	key := make([]byte, 32)
	for i := range key {
		key[i] = byte(i*7 + 1)
	}
	for _, vr := range expVariants {
		if vr.eor3 && !cpu.ARM64HasSHA3 {
			t.Logf("skipping %s: no SHA3", vr.name)
			continue
		}
		for _, keySize := range []int{16, 24, 32} {
			var b Block
			newBlock(&b, key[:keySize])
			for _, ivlo := range []uint64{0, 5, ^uint64(0) - 40} {
				ivhi := uint64(7)
				for nb := 1; nb <= 40; nb++ {
					src := make([]byte, nb*BlockSize+16)
					for i := range src {
						src[i] = byte(i*131 + nb)
					}
					want := ctrReference(key[:keySize], src[:nb*BlockSize], ivlo, ivhi)
					got := make([]byte, len(src))
					copy(got[nb*BlockSize:], src[nb*BlockSize:])
					vr.f(b.rounds, &b.enc, &got[0], &src[0], nb/12, nb%12, ivlo, ivhi)
					if !bytes.Equal(got[:nb*BlockSize], want) || !bytes.Equal(got[nb*BlockSize:], src[nb*BlockSize:]) {
						t.Fatalf("%s key=%d ivlo=%#x nb=%d: wrong output", vr.name, keySize, ivlo, nb)
					}
					vr.f(b.rounds, &b.enc, &src[0], &src[0], nb/12, nb%12, ivlo, ivhi)
					if !bytes.Equal(src[:nb*BlockSize], want) {
						t.Fatalf("%s key=%d ivlo=%#x nb=%d: wrong output in place", vr.name, keySize, ivlo, nb)
					}
				}
			}
		}
	}
}

// BenchmarkExpAsm calls the assembly directly, in place on one buffer (as
// crypto/cipher's benchmarks do), out of place, and in place alternating
// between two buffers. "fixed" is master's sequence of fixed-size calls.
func BenchmarkExpAsm(b *testing.B) {
	if !supportsAES {
		b.Skip("no AES instructions")
	}
	key := make([]byte, 32)
	buf0 := make([]byte, 16*BlockSize)
	buf1 := make([]byte, 16*BlockSize)
	modes := []struct {
		name   string
		dp, sp [2]*byte
		mask   int
	}{
		{"inplace", [2]*byte{&buf0[0], &buf0[0]}, [2]*byte{&buf0[0], &buf0[0]}, 0},
		{"disjoint", [2]*byte{&buf1[0], &buf1[0]}, [2]*byte{&buf0[0], &buf0[0]}, 0},
		{"alt", [2]*byte{&buf0[0], &buf1[0]}, [2]*byte{&buf0[0], &buf1[0]}, 1},
	}
	for _, keySize := range []int{16, 32} {
		var blk Block
		newBlock(&blk, key[:keySize])
		nr, xk := blk.rounds, &blk.enc
		for _, nb := range []int{1, 2, 3, 4, 8, 12} {
			for _, m := range modes {
				dp, sp, mask := m.dp, m.sp, m.mask
				b.Run(fmt.Sprintf("%d/%d/%s/fixed", keySize*8, nb, m.name), func(b *testing.B) {
					b.SetBytes(int64(nb * BlockSize))
					switch nb {
					case 1:
						for i := 0; i < b.N; i++ {
							j := i & mask
							d, s := unsafe.Pointer(dp[j]), unsafe.Pointer(sp[j])
							ctrBlocks1Asm(nr, xk, (*[16]byte)(d), (*[16]byte)(s), uint64(i), 0)
						}
					case 2:
						for i := 0; i < b.N; i++ {
							j := i & mask
							d, s := unsafe.Pointer(dp[j]), unsafe.Pointer(sp[j])
							ctrBlocks2Asm(nr, xk, (*[32]byte)(d), (*[32]byte)(s), uint64(i)*2, 0)
						}
					case 3:
						for i := 0; i < b.N; i++ {
							j := i & mask
							d, s := unsafe.Pointer(dp[j]), unsafe.Pointer(sp[j])
							ctrBlocks2Asm(nr, xk, (*[32]byte)(d), (*[32]byte)(s), uint64(i)*3, 0)
							ctrBlocks1Asm(nr, xk, (*[16]byte)(unsafe.Add(d, 32)), (*[16]byte)(unsafe.Add(s, 32)), uint64(i)*3+2, 0)
						}
					case 4:
						for i := 0; i < b.N; i++ {
							j := i & mask
							d, s := unsafe.Pointer(dp[j]), unsafe.Pointer(sp[j])
							ctrBlocks4Asm(nr, xk, (*[64]byte)(d), (*[64]byte)(s), uint64(i)*4, 0)
						}
					case 8:
						for i := 0; i < b.N; i++ {
							j := i & mask
							d, s := unsafe.Pointer(dp[j]), unsafe.Pointer(sp[j])
							ctrBlocks8Asm(nr, xk, (*[128]byte)(d), (*[128]byte)(s), uint64(i)*8, 0)
						}
					case 12:
						for i := 0; i < b.N; i++ {
							j := i & mask
							d, s := unsafe.Pointer(dp[j]), unsafe.Pointer(sp[j])
							ctrBlocks8Asm(nr, xk, (*[128]byte)(d), (*[128]byte)(s), uint64(i)*12, 0)
							ctrBlocks4Asm(nr, xk, (*[64]byte)(unsafe.Add(d, 128)), (*[64]byte)(unsafe.Add(s, 128)), uint64(i)*12+8, 0)
						}
					}
				})
				for _, vr := range expVariants {
					if vr.eor3 && !cpu.ARM64HasSHA3 {
						continue
					}
					b.Run(fmt.Sprintf("%d/%d/%s/%s", keySize*8, nb, m.name, vr.name), func(b *testing.B) {
						b.SetBytes(int64(nb * BlockSize))
						n, r := nb/12, nb%12
						switch vr.name {
						case "cl":
							for i := 0; i < b.N; i++ {
								j := i & mask
								ctrBlocksBulkAsm(nr, xk, dp[j], sp[j], n, r, uint64(i)*uint64(nb), 0)
							}
						case "clE3":
							for i := 0; i < b.N; i++ {
								j := i & mask
								ctrBlocksBulkEOR3Asm(nr, xk, dp[j], sp[j], n, r, uint64(i)*uint64(nb), 0)
							}
						case "pairs":
							for i := 0; i < b.N; i++ {
								j := i & mask
								ctrBulkPairs(nr, xk, dp[j], sp[j], n, r, uint64(i)*uint64(nb), 0)
							}
						case "ld4":
							for i := 0; i < b.N; i++ {
								j := i & mask
								ctrBulkLd4(nr, xk, dp[j], sp[j], n, r, uint64(i)*uint64(nb), 0)
							}
						case "pre":
							for i := 0; i < b.N; i++ {
								j := i & mask
								ctrBulkPre(nr, xk, dp[j], sp[j], n, r, uint64(i)*uint64(nb), 0)
							}
						case "align":
							for i := 0; i < b.N; i++ {
								j := i & mask
								ctrBulkAlign(nr, xk, dp[j], sp[j], n, r, uint64(i)*uint64(nb), 0)
							}
						case "e3pairs":
							for i := 0; i < b.N; i++ {
								j := i & mask
								ctrBulkE3Pairs(nr, xk, dp[j], sp[j], n, r, uint64(i)*uint64(nb), 0)
							}
						case "e3ld4":
							for i := 0; i < b.N; i++ {
								j := i & mask
								ctrBulkE3Ld4(nr, xk, dp[j], sp[j], n, r, uint64(i)*uint64(nb), 0)
							}
						case "e3pre":
							for i := 0; i < b.N; i++ {
								j := i & mask
								ctrBulkE3Pre(nr, xk, dp[j], sp[j], n, r, uint64(i)*uint64(nb), 0)
							}
						}
					})
				}
			}
		}
	}
}

// BenchmarkExpStream measures the whole Go path, like crypto/cipher's
// benchmarkAESStream (one CTR stream, in place on one buffer).
func BenchmarkExpStream(b *testing.B) {
	key := make([]byte, 32)
	for _, keySize := range []int{16, 32} {
		var blk Block
		newBlock(&blk, key[:keySize])
		for _, nb := range []int{1, 2, 3, 4, 8, 12} {
			b.Run(fmt.Sprintf("%d/%d", keySize*8, nb), func(b *testing.B) {
				buf := make([]byte, nb*BlockSize)
				b.SetBytes(int64(len(buf)))
				c := NewCTR(&blk, make([]byte, BlockSize))
				for i := 0; i < b.N; i++ {
					c.XORKeyStream(buf, buf)
				}
			})
		}
	}
}
