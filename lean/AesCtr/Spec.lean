/-
What Go's arm64 AES-CTR assembly must compute.

This file is the contract. Everything else in the project proves that the
machine code (the exact instruction words the Go assembler emits) meets it when
run in LNSym, a Lean model of the AArch64 instruction set.
-/
import Arm.State
import Arm.Insts.DPSFP.Crypto_aes
import Specs.AESCommon
import Arm.Memory.Separate

namespace AesCtr

open BitVec

/-! ## Blocks

A 16-byte block is a `BitVec 128` whose byte `j` (bits `8j+7 .. 8j`) is the
byte at offset `j` in memory: what `LD1 {Vt.16B}` loads and LNSym's
`read_mem_bytes 16` reads. -/

/-! ## AES (FIPS-197)

The three round transformations are LNSym's definitions, the ones its model of
the `AESE` and `AESMC` instructions is built from. -/

abbrev SubBytes := AESCommon.SubBytes
abbrev ShiftRows := AESCommon.ShiftRows
abbrev MixColumns := DPSFP.AESMixColumns

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

/-! ## The machine-level contract

The assembly functions are Go ABI0 functions: the arguments are on the stack
from `sp + 8`, the return address is in `x30`, and they return with `RET`. A
state `s` of the LNSym model has the registers (`r (.GPR i) s`), the program
counter, an error flag and the memory. -/

/-- The `k`-th 8-byte argument of a call (Go ABI0: the arguments start at `sp + 8`). -/
def arg (s : ArmState) (k : Nat) : BitVec 64 :=
  read_mem_bytes 8 (r (.GPR 31#5) s + BitVec.ofNat 64 (8 + 8 * k)) s

/-- Block `i` of the buffer at `base`: the 16 bytes at `base + 16 i`. -/
def block (s : ArmState) (base : BitVec 64) (i : Nat) : BitVec 128 :=
  read_mem_bytes 16 (base + BitVec.ofNat 64 (16 * i)) s

/-- One call: `nblocks` blocks from `src` to `dst`, round keys at `xk` (round key
`r` is block `r` of the key schedule), initial counter `ivhi * 2^64 + ivlo`. -/
structure Call where
  nr : Nat
  xk : BitVec 64
  dst : BitVec 64
  src : BitVec 64
  nblocks : Nat
  ivlo : BitVec 64
  ivhi : BitVec 64

/-- What the caller guarantees: the code is loaded at address 0 and runs from
its start; `nr` is 10, 12 or 14; `dst` does not overlap the arguments
(`nargs` slots) or the key schedule (`[60]uint32`, 240 bytes); `dst` and `src`
are the same buffer or do not overlap. -/
structure Pre (prog : Program) (nargs : Nat) (c : Call) (s : ArmState) : Prop where
  program : s.program = prog
  pc : r .PC s = 0#64
  err : r .ERR s = .None
  sp_aligned : CheckSPAlignment s
  nr : c.nr = 10 ∨ c.nr = 12 ∨ c.nr = 14
  args_dst : mem_separate' (r (.GPR 31#5) s + 8#64) (8 * nargs) c.dst (16 * c.nblocks)
  keys_dst : mem_separate' c.xk 240 c.dst (16 * c.nblocks)
  src_dst : (c.src = c.dst ∧ mem_legal' c.dst (16 * c.nblocks)) ∨
    mem_separate' c.src (16 * c.nblocks) c.dst (16 * c.nblocks)

/-- What the function guarantees when it returns: no model error, the program
counter is the return address, the registers Go reserves (x18, the goroutine
pointer x28, the frame pointer x29, the link register x30, the stack pointer) are
unchanged, `dst` holds `src` XOR the keystream, and no other memory changed. -/
structure Post (c : Call) (s0 s : ArmState) : Prop where
  err : r .ERR s = .None
  ret : r .PC s = r (.GPR 30#5) s0
  regs : r (.GPR 18#5) s = r (.GPR 18#5) s0 ∧ r (.GPR 28#5) s = r (.GPR 28#5) s0 ∧
    r (.GPR 29#5) s = r (.GPR 29#5) s0 ∧ r (.GPR 30#5) s = r (.GPR 30#5) s0 ∧
    r (.GPR 31#5) s = r (.GPR 31#5) s0
  out : ∀ i < c.nblocks,
    block s c.dst i = block s0 c.src i ^^^ keystream c.nr (block s0 c.xk) c.ivhi c.ivlo i
  frame : ∀ (a : BitVec 64) (n : Nat), mem_separate' a n c.dst (16 * c.nblocks) →
    read_mem_bytes n a s = read_mem_bytes n a s0

/-- The call of `ctrBlocksNAsm(nr int, xk *[60]uint32, dst, src *[N*16]byte,
ivlo, ivhi uint64)` in state `s`. -/
def callN (s : ArmState) (N : Nat) : Call :=
  { nr := (arg s 0).toNat, xk := arg s 1, dst := arg s 2, src := arg s 3, nblocks := N,
    ivlo := arg s 4, ivhi := arg s 5 }

end AesCtr
