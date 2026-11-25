#!/usr/bin/env bash
# Round 3: two-function candidate with the lean Go wrapper.
# Usage: build-variant3.sh <name> <G> <stage> [plain]
#        build-variant3.sh base
set -euo pipefail
name="$1"; shift
W=/root/aesctr
P=$W/proj
EXP=$W/go-exp
AES=src/crypto/internal/fips140/aes
export PATH=$EXP/bin:$PATH GOFLAGS=-count=1
rsync -a --delete $W/go-base/$AES/ $EXP/$AES/
rsync -a $W/go-base/src/crypto/cipher/ $EXP/src/crypto/cipher/
cp $P/exp/cipher/ctr_extra_test.go $EXP/src/crypto/cipher/
if [ "$name" != base ]; then
  G="$1"; stage="$2"; plain="${3:-}"
  cp $P/exp/aes3/*.go $EXP/$AES/
  sed -i "s|n/12|n/$G|g; s|n%12|n%$G|g" $EXP/$AES/ctr_bulk_arm64.go
  if [ "$plain" = plain ]; then
    sed -i 's|^var supportsAESEOR3 = supportsAES \&\& cpu.ARM64HasSHA3|var supportsAESEOR3 = false \&\& cpu.ARM64HasSHA3|' $EXP/$AES/ctr_bulk_arm64.go
  fi
  python3 $P/tools/gen_ctr_asm3.py --blocks "$G" --stage "$stage" $W/go-base/$AES/ctr_arm64.s > $EXP/$AES/ctr_arm64.s
fi
mkdir -p $W/out/$name
cp $EXP/$AES/ctr_arm64.s $EXP/$AES/*.go $W/out/$name/ 2>/dev/null || true
cd $EXP/src
GOARCH=arm64 go vet crypto/internal/fips140/aes crypto/cipher
GOARCH=arm64 go build -gcflags=crypto/internal/fips140/aes=-m crypto/internal/fips140/aes 2>&1 | grep -E "ctr_bulk_arm64.go|ctr.go:9[0-9]|ctr.go:1[01][0-9]" | grep -i "inlin" | head -20 || true
GOARCH=arm64 go test -c -o $W/out/$name/cipher.test crypto/cipher
echo "built $name"
