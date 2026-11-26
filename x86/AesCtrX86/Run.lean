/-
Runs `ctrBlocksBulkAsm` in Kraken's evaluator and compares what it writes with
the spec: a test of the parsed program and of the model, not a proof.
-/
import AesCtrX86.Spec
import AesCtrX86.KAT
import AesCtrX86.Layout

open Std

namespace AesCtrX86

/-- The 16 bytes of a block, in memory order. -/
def blockBytes (x : BitVec 128) : List UInt8 :=
  (List.range 16).map fun j => (x.extractLsb' (8 * j) 8).toNat.toUInt8

/-- The 8 bytes of `x`, little-endian. -/
def u64Bytes (x : UInt64) : List UInt8 :=
  (List.range 8).map fun j => ((x >>> (8 * j).toUInt64) &&& 0xff).toUInt8

/-- One test call of `ctrBlocksBulkAsm`. -/
structure Case where
  nr : Nat
  rk : Nat → BitVec 128
  n : Nat
  ivlo : UInt64
  ivhi : UInt64
  vaes : Bool
  inPlace : Bool
  seed : UInt64

def Case.describe (c : Case) : String :=
  s!"nr={c.nr} n={c.n} vaes={c.vaes} inPlace={c.inPlace} ivhi={c.ivhi} ivlo={c.ivlo}"

def retAddr : Int64 := 0x1337
def rspAddr : UInt64 := 0x7fff0000
def xkAddr : UInt64 := 0x10000000
def srcAddr : UInt64 := 0x20000000
def dstAddr (c : Case) : UInt64 := if c.inPlace then srcAddr else 0x30000000

/-- Pseudo-random source blocks. -/
def srcBlocks (c : Case) : List (BitVec 128) := Id.run do
  let mut x := c.seed
  let mut out := []
  for _ in [0:c.n] do
    x := x * 6364136223846793005 + 1442695040888963407
    let lo := x
    x := x * 6364136223846793005 + 1442695040888963407
    out := out ++ [(BitVec.ofNat 64 x.toNat) ++ (BitVec.ofNat 64 lo.toNat)]
  return out

/-- The data of the program (`bswapMask`, `ctrOffsets`) at its addresses. -/
def dataMem : Mem 64 :=
  exe.withAddresses.foldl (fun m (a, d, _) =>
    match d with
    | .byteArray bs => Mem.storeBytes m a.toBitVec bs.data.toList
    | _ => m) ∅

def initMem (c : Case) : Mem 64 :=
  let args := u64Bytes retAddr.toUInt64 ++ u64Bytes c.nr.toUInt64 ++ u64Bytes xkAddr ++
    u64Bytes (dstAddr c) ++ u64Bytes srcAddr ++ u64Bytes c.n.toUInt64 ++ u64Bytes c.ivlo ++
    u64Bytes c.ivhi ++ u64Bytes (if c.vaes then 1 else 0)
  let keys := ((List.range 15).map fun i => if i ≤ c.nr then blockBytes (c.rk i) else
    List.replicate 16 0).flatten
  let src := ((srcBlocks c).map blockBytes).flatten
  let m := Mem.storeBytes dataMem rspAddr.toBitVec args
  let m := Mem.storeBytes m xkAddr.toBitVec keys
  let m := if c.inPlace then m else
    Mem.storeBytes m (dstAddr c).toBitVec (List.replicate (16 * c.n) 0xaa)
  Mem.storeBytes m srcAddr.toBitVec src

/-- Runs the case; `ok true` if `dst` holds `src` XOR the keystream and the
function returned to the caller with the stack pointer restored. -/
def runCase (c : Case) : Except String Bool := do
  let s0 : MachineData := { regs := { rsp := rspAddr }, dmem := initMem c }
  let (s, pc) ← Executable.eval exe (s0, entry_bulk) (fun (_, pc) => pc == retAddr)
  let src := srcBlocks c
  let ok := (List.range c.n).all fun i =>
    let want := src[i]! ^^^ keystream c.nr c.rk (BitVec.ofNat 64 c.ivhi.toNat)
      (BitVec.ofNat 64 c.ivlo.toNat) i
    Mem.loadBytes s.dmem ((dstAddr c).toBitVec + BitVec.ofNat 64 (16 * i)) 16 ==
      some (blockBytes want)
  return ok && pc == retAddr && s.regs.rsp == rspAddr + 8

def keySchedules : List (Nat × (Nat → BitVec 128)) :=
  [(10, c1Keys), (12, c2Keys), (14, c3Keys)]

def testSizes : List Nat := (List.range 41).drop 1 ++ [47, 48, 49, 63, 64, 65]

/-- Every key size, both paths, every size above, three initial counters (the
last two end the low 64 bits exactly at 2^64 - 1 and start them at 0), each
both in place and not. -/
def cases : List Case := Id.run do
  let mut out := []
  for (nr, rk) in keySchedules do
    for vaes in [false, true] do
      for n in testSizes do
        for (ivhi, ivlo) in [(0x0123456789abcdef, 0xfedcba9876543210),
            (0xfffffffffffffffe, (0 : UInt64) - n.toUInt64), (0xffffffffffffffff, 0)] do
          for inPlace in [false, true] do
            let seed := (nr * 1000 + n).toUInt64
            out := out ++ [Case.mk nr rk n ivlo ivhi vaes inPlace seed]
  return out

end AesCtrX86
