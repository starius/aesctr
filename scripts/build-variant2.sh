#!/usr/bin/env bash
# Round 2: build one variant into the experiment Go tree; arm64 test binaries.
# Usage: build-variant2.sh <name> <go|asm|control> [gen_ctr_asm2.py options...]
#        build-variant2.sh base
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
  mode="$1"; shift
  cp $P/exp/aes2/*.go $EXP/$AES/
  python3 $P/tools/gen_ctr_asm2.py "$@" $([ "$mode" = asm ] && echo --tail asm) $W/go-base/$AES/ctr_arm64.s > $EXP/$AES/ctr_arm64.s
  G=$(grep -o "blocks=[0-9]*" $EXP/$AES/ctr_arm64.s | cut -d= -f2)
  tail=false; [ "$mode" = asm ] && tail=true
  printf "//go:build !purego\n\npackage aes\n\nconst ctrGroupBlocks = %s\nconst ctrAsmTail = %s\n" "$G" "$tail" > $EXP/$AES/ctr_group_arm64.go
  if [ "$mode" = control ]; then
    sed -i 's/\tif !supportsAES {\n\t\tctrBlocksNGeneric/XX/' $EXP/$AES/ctr_n_arm64.go
    sed -i '0,/\tif !supportsAES {/s//\tif !supportsAES || true {/' $EXP/$AES/ctr_n_arm64.go
  fi
fi
mkdir -p $W/out/$name
cp $EXP/$AES/ctr_arm64.s $W/out/$name/
cd $EXP/src
GOARCH=arm64 go vet crypto/internal/fips140/aes
GOARCH=arm64 go test -c -o $W/out/$name/cipher.test crypto/cipher
echo "built $name"
