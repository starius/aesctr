// Experiment only.

package cipher_test

import (
	"crypto/internal/fips140/aes"
	"fmt"
	"os"
	"strconv"
)

func init() {
	s := os.Getenv("CTRV")
	if s == "" {
		return
	}
	v, err := strconv.Atoi(s)
	if err != nil || !aes.SetCTRVariant(v) {
		fmt.Fprintf(os.Stderr, "CTRV=%s: unsupported variant\n", s)
		os.Exit(3)
	}
}
