/-
What Go's amd64 AES-CTR assembly must compute: the same mathematical contract
as the arm64 proofs (aesctr/lean/AesCtr/Spec.lean), with the same FIPS-197
round functions.

The round functions are LNSym's (Specs/AESCommon.lean,
Arm/Insts/DPSFP/Crypto_aes.lean and Arm/BitVec.lean; Copyright (c) 2023
Amazon.com, Inc. or its affiliates; Apache 2.0), copied unchanged in the
namespace `AesCtrX86.LNSym` so that this project does not depend on LNSym.
-/

namespace AesCtrX86

open BitVec

namespace LNSym

/-- LNSym's `BitVec.flatten`. -/
protected def flatten {n : Nat} (xs : List (BitVec n)) : BitVec (n * xs.length) :=
  match xs with
  | [] => 0#0
  | x :: rest =>
    have h : n + n * List.length rest = n * List.length (x :: rest) := by
      simp only [List.length_cons, Nat.mul_add, Nat.mul_one]; omega
    BitVec.cast h (x ++ (LNSym.flatten rest))

/-- LNSym's `BitVec.partInstall`: `x` with bits `start .. start+len` set to
`val`. -/
abbrev partInstall {n : Nat} (start len : Nat) (val : BitVec len) (x : BitVec n) : BitVec n :=
  let mask := allOnes len
  let val_aligned := (setWidth n val) <<< start
  let mask_with_hole := ~~~ ((setWidth n mask) <<< start)
  let x_with_hole := x &&& mask_with_hole
  x_with_hole ||| val_aligned

def SBOX :=
  --   F E D C B A 9 8 7 6 5 4 3 2 1 0
  [ 0x16bb54b00f2d99416842e6bf0d89a18c#128, -- F
    0xdf2855cee9871e9b948ed9691198f8e1#128, -- E
    0x9e1dc186b95735610ef6034866b53e70#128, -- D
    0x8a8bbd4b1f74dde8c6b4a61c2e2578ba#128, -- C
    0x08ae7a65eaf4566ca94ed58d6d37c8e7#128, -- B
    0x79e4959162acd3c25c2406490a3a32e0#128, -- A
    0xdb0b5ede14b8ee4688902a22dc4f8160#128, -- 9
    0x73195d643d7ea7c41744975fec130ccd#128, -- 8
    0xd2f3ff1021dab6bcf5389d928f40a351#128, -- 7
    0xa89f3c507f02f94585334d43fbaaefd0#128, -- 6
    0xcf584c4a39becb6a5bb1fc20ed00d153#128, -- 5
    0x842fe329b3d63b52a05a6e1b1a2c8309#128, -- 4
    0x75b227ebe28012079a059618c323c704#128, -- 3
    0x1531d871f1e5a534ccf73f362693fdb7#128, -- 2
    0xc072a49cafa2d4adf04759fa7dc982ca#128, -- 1
    0x76abd7fe2b670130c56f6bf27b777c63#128  -- 0
  ]

def ShiftRows (op : BitVec 128) : BitVec 128 :=
  extractLsb' 88 8 op ++ extractLsb' 48 8 op ++
  extractLsb' 8 8 op ++ extractLsb' 96 8 op ++
  extractLsb' 56 8 op ++ extractLsb' 16 8 op ++
  extractLsb' 104 8 op ++ extractLsb' 64 8 op ++
  extractLsb' 24 8 op ++ extractLsb' 112 8 op ++
  extractLsb' 72 8 op ++ extractLsb' 32 8 op ++
  extractLsb' 120 8 op ++ extractLsb' 80 8 op ++
  extractLsb' 40 8 op ++ extractLsb' 0 8 op

def SubBytes_aux (i : Nat) (op : BitVec 128) (out : BitVec 128)
  : BitVec 128 :=
  match i with
  | 0 => out
  | i' + 1 =>
    let i := 16 - i
    let idx := (extractLsb' (i * 8) 8 op).toNat
    let val := extractLsb' (idx * 8) 8 $ LNSym.flatten SBOX
    let out := partInstall (i * 8) 8 val out
    SubBytes_aux i' op out

def SubBytes (op : BitVec 128) : BitVec 128 :=
  SubBytes_aux 16 op (BitVec.zero 128)

def MixColumns_aux (c : Nat)
  (in0 : BitVec 32) (in1 : BitVec 32) (in2 : BitVec 32) (in3 : BitVec 32)
  (out0 : BitVec 32) (out1 : BitVec 32) (out2 : BitVec 32) (out3 : BitVec 32)
  (FFmul02 : BitVec 8 -> BitVec 8) (FFmul03 : BitVec 8 -> BitVec 8)
  : BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 :=
  match c with
  | 0 => (out0, out1, out2, out3)
  | c' + 1 =>
    let lo := (4 - c) * 8
    let in0_byte := extractLsb' lo 8 in0
    let in1_byte := extractLsb' lo 8 in1
    let in2_byte := extractLsb' lo 8 in2
    let in3_byte := extractLsb' lo 8 in3
    let val0 := FFmul02 in0_byte ^^^ FFmul03 in1_byte ^^^ in2_byte ^^^ in3_byte
    let out0 := partInstall lo 8 val0 out0
    let val1 := FFmul02 in1_byte ^^^ FFmul03 in2_byte ^^^ in3_byte ^^^ in0_byte
    let out1 := partInstall lo 8 val1 out1
    let val2 := FFmul02 in2_byte ^^^ FFmul03 in3_byte ^^^ in0_byte ^^^ in1_byte
    let out2 := partInstall lo 8 val2 out2
    let val3 := FFmul02 in3_byte ^^^ FFmul03 in0_byte ^^^ in1_byte ^^^ in2_byte
    let out3 := partInstall lo 8 val3 out3
    MixColumns_aux c' in0 in1 in2 in3 out0 out1 out2 out3 FFmul02 FFmul03

def MixColumns (op : BitVec 128) (FFmul02 : BitVec 8 -> BitVec 8)
  (FFmul03 : BitVec 8 -> BitVec 8) : BitVec 128 :=
  let in0 :=
    extractLsb' 96 8 op ++ extractLsb' 64 8 op ++
    extractLsb' 32 8 op ++ extractLsb' 0 8 op
  let in1 :=
    extractLsb' 104 8 op ++ extractLsb' 72 8 op ++
    extractLsb' 40 8 op ++ extractLsb' 8 8 op
  let in2 :=
    extractLsb' 112 8 op ++ extractLsb' 80 8 op ++
    extractLsb' 48 8 op ++ extractLsb' 16 8 op
  let in3 :=
    extractLsb' 120 8 op ++ extractLsb' 88 8 op ++
    extractLsb' 56 8 op ++ extractLsb' 24 8 op
  let (out0, out1, out2, out3) :=
    (BitVec.zero 32, BitVec.zero 32,
     BitVec.zero 32, BitVec.zero 32)
  let (out0, out1, out2, out3) :=
    MixColumns_aux 4 in0 in1 in2 in3 out0 out1 out2 out3 FFmul02 FFmul03
  extractLsb' 24 8 out3 ++ extractLsb' 24 8 out2 ++
  extractLsb' 24 8 out1 ++ extractLsb' 24 8 out0 ++
  extractLsb' 16 8 out3 ++ extractLsb' 16 8 out2 ++
  extractLsb' 16 8 out1 ++ extractLsb' 16 8 out0 ++
  extractLsb' 8 8 out3 ++ extractLsb' 8 8 out2 ++
  extractLsb' 8 8 out1 ++ extractLsb' 8 8 out0 ++
  extractLsb' 0 8 out3 ++ extractLsb' 0 8 out2 ++
  extractLsb' 0 8 out1 ++ extractLsb' 0 8 out0

def FFmul02 (b : BitVec 8) : BitVec 8 :=
  let FFmul_02 :=
    --   F E D C B A 9 8 7 6 5 4 3 2 1 0
    [ 0xE5E7E1E3EDEFE9EBF5F7F1F3FDFFF9FB#128, -- F
      0xC5C7C1C3CDCFC9CBD5D7D1D3DDDFD9DB#128, -- E
      0xA5A7A1A3ADAFA9ABB5B7B1B3BDBFB9BB#128, -- D
      0x858781838D8F898B959791939D9F999B#128, -- C
      0x656761636D6F696B757771737D7F797B#128, -- B
      0x454741434D4F494B555751535D5F595B#128, -- A
      0x252721232D2F292B353731333D3F393B#128, -- 9
      0x050701030D0F090B151711131D1F191B#128, -- 8
      0xFEFCFAF8F6F4F2F0EEECEAE8E6E4E2E0#128, -- 7
      0xDEDCDAD8D6D4D2D0CECCCAC8C6C4C2C0#128, -- 6
      0xBEBCBAB8B6B4B2B0AEACAAA8A6A4A2A0#128, -- 5
      0x9E9C9A98969492908E8C8A8886848280#128, -- 4
      0x7E7C7A78767472706E6C6A6866646260#128, -- 3
      0x5E5C5A58565452504E4C4A4846444240#128, -- 2
      0x3E3C3A38363432302E2C2A2826242220#128, -- 1
      0x1E1C1A18161412100E0C0A0806040200#128  -- 0
    ]
  let lo := b.toNat * 8
  extractLsb' lo 8 $ LNSym.flatten FFmul_02

def FFmul03 (b : BitVec 8) : BitVec 8 :=
  let FFmul_03 :=
    --   F E D C B A 9 8 7 6 5 4 3 2 1 0
    [ 0x1A191C1F16151013020104070E0D080B#128, -- F
      0x2A292C2F26252023323134373E3D383B#128, -- E
      0x7A797C7F76757073626164676E6D686B#128, -- D
      0x4A494C4F46454043525154575E5D585B#128, -- C
      0xDAD9DCDFD6D5D0D3C2C1C4C7CECDC8CB#128, -- B
      0xEAE9ECEFE6E5E0E3F2F1F4F7FEFDF8FB#128, -- A
      0xBAB9BCBFB6B5B0B3A2A1A4A7AEADA8AB#128, -- 9
      0x8A898C8F86858083929194979E9D989B#128, -- 8
      0x818287848D8E8B88999A9F9C95969390#128, -- 7
      0xB1B2B7B4BDBEBBB8A9AAAFACA5A6A3A0#128, -- 6
      0xE1E2E7E4EDEEEBE8F9FAFFFCF5F6F3F0#128, -- 5
      0xD1D2D7D4DDDEDBD8C9CACFCCC5C6C3C0#128, -- 4
      0x414247444D4E4B48595A5F5C55565350#128, -- 3
      0x717277747D7E7B78696A6F6C65666360#128, -- 2
      0x212227242D2E2B28393A3F3C35363330#128, -- 1
      0x111217141D1E1B18090A0F0C05060300#128  -- 0
    ]
  let lo := b.toNat * 8
  extractLsb' lo 8 $ LNSym.flatten FFmul_03

def AESMixColumns (op : BitVec 128) : BitVec 128 :=
  MixColumns op FFmul02 FFmul03

end LNSym

/-! ## Blocks

A 16-byte block is a `BitVec 128` whose byte `j` (bits `8j+7 .. 8j`) is the
byte at offset `j` in memory: what `MOVDQU` loads into an XMM register. -/

/-! ## AES (FIPS-197) -/

abbrev SubBytes := LNSym.SubBytes
abbrev ShiftRows := LNSym.ShiftRows
abbrev MixColumns := LNSym.AESMixColumns

/-- The AES state after the initial AddRoundKey and rounds `1 .. r`
(FIPS-197, `Cipher`, for `r < nr`). `rk i` is round key `i`. -/
def aesState (rk : Nat → BitVec 128) (x : BitVec 128) : Nat → BitVec 128
  | 0 => x ^^^ rk 0
  | r + 1 => MixColumns (ShiftRows (SubBytes (aesState rk x r))) ^^^ rk (r + 1)

/-- AES encryption of block `x` with `nr` rounds (10, 12 or 14) and round keys
`rk 0 .. rk nr`. The last round has no MixColumns. -/
def aesEncrypt (nr : Nat) (rk : Nat → BitVec 128) (x : BitVec 128) : BitVec 128 :=
  ShiftRows (SubBytes (aesState rk x (nr - 1))) ^^^ rk nr

/-! ## Counter mode -/

/-- The 8 bytes of `x`, most significant first (big-endian): byte 0 of the
result is the top byte of `x`. -/
def bswap64 (x : BitVec 64) : BitVec 64 :=
  x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8 ++
  x.extractLsb' 32 8 ++ x.extractLsb' 40 8 ++ x.extractLsb' 48 8 ++ x.extractLsb' 56 8

/-- The counter block for the 128-bit counter value `c`: its 16 bytes are `c`,
big-endian. -/
def counterBlock (c : BitVec 128) : BitVec 128 :=
  bswap64 (c.extractLsb' 0 64) ++ bswap64 (c.extractLsb' 64 64)

/-- Keystream block `i`: the encryption of counter `iv + i`, where the 128-bit
initial counter is `iv = ivhi * 2^64 + ivlo`. The counter wraps modulo `2^128`
(`add128` in ctr.go). -/
def keystream (nr : Nat) (rk : Nat → BitVec 128) (ivhi ivlo : BitVec 64) (i : Nat) :
    BitVec 128 :=
  aesEncrypt nr rk (counterBlock ((ivhi ++ ivlo) + BitVec.ofNat 128 i))

end AesCtrX86
