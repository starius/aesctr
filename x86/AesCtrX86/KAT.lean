/-
Known-answer tests for the spec's AES: FIPS-197 Appendix C.1, C.2 and C.3
(AES-128, AES-192, AES-256), checked by the kernel (`decide +kernel`). Blocks
are written as FIPS-197 prints them (first byte first) and converted to the
spec's byte order by `ofHex`. The round keys are FIPS-197's `round[r].k_sch`.
-/
import AesCtrX86.Spec

namespace AesCtrX86

set_option maxRecDepth 100000

/-- A block written as FIPS-197 prints it (first byte most significant):
the same conversion as a counter block. -/
abbrev ofHex (x : BitVec 128) : BitVec 128 := counterBlock x

/-- FIPS-197 C.1: the key schedule of key 000102...0f. -/
def c1Keys : Nat → BitVec 128
  | 0 => ofHex 0x000102030405060708090a0b0c0d0e0f#128
  | 1 => ofHex 0xd6aa74fdd2af72fadaa678f1d6ab76fe#128
  | 2 => ofHex 0xb692cf0b643dbdf1be9bc5006830b3fe#128
  | 3 => ofHex 0xb6ff744ed2c2c9bf6c590cbf0469bf41#128
  | 4 => ofHex 0x47f7f7bc95353e03f96c32bcfd058dfd#128
  | 5 => ofHex 0x3caaa3e8a99f9deb50f3af57adf622aa#128
  | 6 => ofHex 0x5e390f7df7a69296a7553dc10aa31f6b#128
  | 7 => ofHex 0x14f9701ae35fe28c440adf4d4ea9c026#128
  | 8 => ofHex 0x47438735a41c65b9e016baf4aebf7ad2#128
  | 9 => ofHex 0x549932d1f08557681093ed9cbe2c974e#128
  | _ => ofHex 0x13111d7fe3944a17f307a78b4d2b30c5#128

/-- FIPS-197 C.2: the key schedule of key 000102...17. -/
def c2Keys : Nat → BitVec 128
  | 0 => ofHex 0x000102030405060708090a0b0c0d0e0f#128
  | 1 => ofHex 0x10111213141516175846f2f95c43f4fe#128
  | 2 => ofHex 0x544afef55847f0fa4856e2e95c43f4fe#128
  | 3 => ofHex 0x40f949b31cbabd4d48f043b810b7b342#128
  | 4 => ofHex 0x58e151ab04a2a5557effb5416245080c#128
  | 5 => ofHex 0x2ab54bb43a02f8f662e3a95d66410c08#128
  | 6 => ofHex 0xf501857297448d7ebdf1c6ca87f33e3c#128
  | 7 => ofHex 0xe510976183519b6934157c9ea351f1e0#128
  | 8 => ofHex 0x1ea0372a995309167c439e77ff12051e#128
  | 9 => ofHex 0xdd7e0e887e2fff68608fc842f9dcc154#128
  | 10 => ofHex 0x859f5f237a8d5a3dc0c02952beefd63a#128
  | 11 => ofHex 0xde601e7827bcdf2ca223800fd8aeda32#128
  | _ => ofHex 0xa4970a331a78dc09c418c271e3a41d5d#128

/-- FIPS-197 C.3: the key schedule of key 000102...1f. -/
def c3Keys : Nat → BitVec 128
  | 0 => ofHex 0x000102030405060708090a0b0c0d0e0f#128
  | 1 => ofHex 0x101112131415161718191a1b1c1d1e1f#128
  | 2 => ofHex 0xa573c29fa176c498a97fce93a572c09c#128
  | 3 => ofHex 0x1651a8cd0244beda1a5da4c10640bade#128
  | 4 => ofHex 0xae87dff00ff11b68a68ed5fb03fc1567#128
  | 5 => ofHex 0x6de1f1486fa54f9275f8eb5373b8518d#128
  | 6 => ofHex 0xc656827fc9a799176f294cec6cd5598b#128
  | 7 => ofHex 0x3de23a75524775e727bf9eb45407cf39#128
  | 8 => ofHex 0x0bdc905fc27b0948ad5245a4c1871c2f#128
  | 9 => ofHex 0x45f5a66017b2d387300d4d33640a820a#128
  | 10 => ofHex 0x7ccff71cbeb4fe5413e6bbf0d261a7df#128
  | 11 => ofHex 0xf01afafee7a82979d7a5644ab3afe640#128
  | 12 => ofHex 0x2541fe719bf500258813bbd55a721c0a#128
  | 13 => ofHex 0x4e5a6699a9f24fe07e572baacdf8cdea#128
  | _ => ofHex 0x24fc79ccbf0979e9371ac23c6d68de36#128

/-- FIPS-197 C.1: AES-128 of 00112233...ff is 69c4e0d8...5a. -/
theorem kat_fips197_c1 :
    aesEncrypt 10 c1Keys (ofHex 0x00112233445566778899aabbccddeeff#128) =
      ofHex 0x69c4e0d86a7b0430d8cdb78070b4c55a#128 := by
  decide +kernel

/-- FIPS-197 C.2: AES-192 of 00112233...ff is dda97ca4...91. -/
theorem kat_fips197_c2 :
    aesEncrypt 12 c2Keys (ofHex 0x00112233445566778899aabbccddeeff#128) =
      ofHex 0xdda97ca4864cdfe06eaf70a0ec0d7191#128 := by
  decide +kernel

/-- FIPS-197 C.3: AES-256 of 00112233...ff is 8ea2b7ca...89. -/
theorem kat_fips197_c3 :
    aesEncrypt 14 c3Keys (ofHex 0x00112233445566778899aabbccddeeff#128) =
      ofHex 0x8ea2b7ca516745bfeafc49904b496089#128 := by
  decide +kernel

end AesCtrX86
