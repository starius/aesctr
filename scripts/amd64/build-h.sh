#!/usr/bin/env bash
# Generates the h variants in go-gen, makes trees from go-amd64g, builds the
# test binaries ($W/x1/h/<v>-bulk.go is exp/amd64/<v>/ctr_amd64_bulk.go). d1: g with ctrBulk false below 8 blocks without VAES.
set -euo pipefail
W=/root/aesctr
C=src/crypto/internal/fips140/aes
GEN=$W/go-gen/$C/_asm/ctr
cd $GEN
for v in h1 h2; do
  cp $W/x1/h/$v-bulk.go ctr_amd64_bulk.go
  (export PATH=$W/go-gen/bin:$PATH GOPATH=$W/gopath GOFLAGS=-mod=mod GOTOOLCHAIN=local; timeout 900 go run . -out $W/x1/h/$v-ctr_amd64.s)
  echo "gen $v: $(wc -l < $W/x1/h/$v-ctr_amd64.s) lines"
done
cp $W/go-amd64g/$C/_asm/ctr/ctr_amd64_bulk.go ctr_amd64_bulk.go
for v in h1 h2 d1; do
  rm -rf $W/go-amd64$v
  cp -al $W/go-amd64g $W/go-amd64$v
done
for v in h1 h2; do
  cp --remove-destination $W/x1/h/$v-ctr_amd64.s $W/go-amd64$v/$C/ctr_amd64.s
  cp --remove-destination $W/x1/h/$v-bulk.go $W/go-amd64$v/$C/_asm/ctr/ctr_amd64_bulk.go
done
f=$W/go-amd64d1/$C/ctr_amd64.go
sed 's/return supportsAES \&\& n > 0 \&\& n-1 <= ^ivlo$/return supportsAES \&\& n > 0 \&\& n-1 <= ^ivlo \&\& (supportsVAES || n >= 8)/' $f > $f.new
mv $f.new $f
grep -n "func ctrBulk" -A 2 $f
for v in h1 h2 d1; do
  cd $W/go-amd64$v/src
  export GOTOOLCHAIN=local
  ../bin/go vet crypto/internal/fips140/aes
  timeout 1200 ../bin/go test -count=1 -short crypto/cipher crypto/internal/fips140/aes 2>&1 | tail -2
  mkdir -p $W/out/x86-$v
  ../bin/go test -c -o $W/out/x86-$v/cipher.test crypto/cipher
  ../bin/go test -c -o $W/out/x86-$v/aes.test crypto/internal/fips140/aes
  echo "built $v"
done
