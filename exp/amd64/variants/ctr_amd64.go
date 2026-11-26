// Experiment only.

//go:build !purego

package aes

import "crypto/internal/fips140deps/cpu"

// ctrVariant selects the bulk function; 0 is master's loop.
var ctrVariant = 0

// CTRVariants maps the experiment's variants to their names.
var CTRVariants = map[int]string{1: "ctrBulkXmm8f", 2: "ctrBulkXmm8", 3: "ctrBulkYmm4f", 4: "ctrBulkYmm6f", 5: "ctrBulkYmm8f", 6: "ctrBulkYmm8", 7: "ctrBulkZmm4f", 8: "ctrBulkZmm6f", 9: "ctrBulkZmm8f", 10: "ctrBulkZmm4", 11: "ctrBulkEy8f", 12: "ctrBulkEy4f"}

// SetCTRVariant selects a variant; it reports whether the CPU supports it.
func SetCTRVariant(v int) bool {
	if v != 0 && !ctrVariantSupported(v) {
		return false
	}
	ctrVariant = v
	return true
}

func ctrVariantSupported(v int) bool {
	switch v {
	case 1:
		return supportsAES
	case 2:
		return supportsAES
	case 3:
		return supportsAES && cpu.X86HasVAES && cpu.X86HasAVX2
	case 4:
		return supportsAES && cpu.X86HasVAES && cpu.X86HasAVX2
	case 5:
		return supportsAES && cpu.X86HasVAES && cpu.X86HasAVX2
	case 6:
		return supportsAES && cpu.X86HasVAES && cpu.X86HasAVX2
	case 7:
		return supportsAES && cpu.X86HasAVX512VAES
	case 8:
		return supportsAES && cpu.X86HasAVX512VAES
	case 9:
		return supportsAES && cpu.X86HasAVX512VAES
	case 10:
		return supportsAES && cpu.X86HasAVX512VAES
	case 11:
		return supportsAES && cpu.X86HasAVX512VAES
	case 12:
		return supportsAES && cpu.X86HasAVX512VAES
	}
	return false
}

func ctrBulk(n, ivlo uint64) bool {
	return ctrVariant != 0 && n > 0 && n-1 <= ^ivlo
}

const supportsAESEOR3 = false

//go:noescape
func ctrBulkXmm8f(nr int, xk *[60]uint32, dst, src *byte, n int, ivlo, ivhi uint64)

//go:noescape
func ctrBulkXmm8(nr int, xk *[60]uint32, dst, src *byte, n int, ivlo, ivhi uint64)

//go:noescape
func ctrBulkYmm4f(nr int, xk *[60]uint32, dst, src *byte, n int, ivlo, ivhi uint64)

//go:noescape
func ctrBulkYmm6f(nr int, xk *[60]uint32, dst, src *byte, n int, ivlo, ivhi uint64)

//go:noescape
func ctrBulkYmm8f(nr int, xk *[60]uint32, dst, src *byte, n int, ivlo, ivhi uint64)

//go:noescape
func ctrBulkYmm8(nr int, xk *[60]uint32, dst, src *byte, n int, ivlo, ivhi uint64)

//go:noescape
func ctrBulkZmm4f(nr int, xk *[60]uint32, dst, src *byte, n int, ivlo, ivhi uint64)

//go:noescape
func ctrBulkZmm6f(nr int, xk *[60]uint32, dst, src *byte, n int, ivlo, ivhi uint64)

//go:noescape
func ctrBulkZmm8f(nr int, xk *[60]uint32, dst, src *byte, n int, ivlo, ivhi uint64)

//go:noescape
func ctrBulkZmm4(nr int, xk *[60]uint32, dst, src *byte, n int, ivlo, ivhi uint64)

//go:noescape
func ctrBulkEy8f(nr int, xk *[60]uint32, dst, src *byte, n int, ivlo, ivhi uint64)

//go:noescape
func ctrBulkEy4f(nr int, xk *[60]uint32, dst, src *byte, n int, ivlo, ivhi uint64)

