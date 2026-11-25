// Experiment only: tail variants of the bulk functions.

//go:build !purego

package aes

//go:noescape
func ctrBulkPairs(nr int, xk *[60]uint32, dst, src *byte, n, r int, ivlo, ivhi uint64)

//go:noescape
func ctrBulkLd4(nr int, xk *[60]uint32, dst, src *byte, n, r int, ivlo, ivhi uint64)

//go:noescape
func ctrBulkPre(nr int, xk *[60]uint32, dst, src *byte, n, r int, ivlo, ivhi uint64)

//go:noescape
func ctrBulkAlign(nr int, xk *[60]uint32, dst, src *byte, n, r int, ivlo, ivhi uint64)

//go:noescape
func ctrBulkE3Pairs(nr int, xk *[60]uint32, dst, src *byte, n, r int, ivlo, ivhi uint64)

//go:noescape
func ctrBulkE3Ld4(nr int, xk *[60]uint32, dst, src *byte, n, r int, ivlo, ivhi uint64)

//go:noescape
func ctrBulkE3Pre(nr int, xk *[60]uint32, dst, src *byte, n, r int, ivlo, ivhi uint64)
