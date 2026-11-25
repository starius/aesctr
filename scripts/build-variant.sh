#!/usr/bin/env bash
# Build one experimental AES-CTR variant into the experiment Go tree and
# produce arm64 test binaries for it. Run inside the dev shell on the builder.
#
# Usage: build-variant.sh <name> [gen_ctr_asm.py options...]
#        build-variant.sh base      (the unmodified tree)
set -euo pipefail
name="$1"; shift
W=/root/aesctr
P=$W/proj
EXP=$W/go-exp
AES=src/crypto/internal/fips140/aes
export PATH=$EXP/bin:$PATH GOFLAGS=-count=1
# Restore the package from the baseline tree, then overlay the variant.
rsync -a --delete $W/go-base/$AES/ $EXP/$AES/
if [ "$name" != base ]; then
  cp $P/exp/aes/*.go $EXP/$AES/
  python3 $P/tools/gen_ctr_asm.py "$@" $W/go-base/$AES/ctr_arm64.s > $EXP/$AES/ctr_arm64.s
  G=$(grep -o "blocks=[0-9]*" $EXP/$AES/ctr_arm64.s | cut -d= -f2)
  printf "//go:build !purego\n\npackage aes\n\nconst ctrGroupBlocks = %s\n" "$G" > $EXP/$AES/ctr_group_arm64.go
fi
mkdir -p $W/out/$name
cp $EXP/$AES/ctr_arm64.s $W/out/$name/
cd $EXP/src
GOARCH=arm64 go vet crypto/internal/fips140/aes
GOARCH=arm64 go test -c -o $W/out/$name/cipher.test crypto/cipher
GOARCH=arm64 go test -c -o $W/out/$name/fipsaes.test crypto/internal/fips140/aes
echo "built $name"
