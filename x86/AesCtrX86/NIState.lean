/-
The state of the AES-NI path of `ctrBlocksBulkAsm` between groups of blocks
(`NIRegs`), the memory facts a group needs, derived from what the caller
guarantees, and what the proofs of all the functions share: what holds when a
function returns (`Post`).
-/
import AesCtrX86.Contract
import AesCtrX86.Final
import Kraken.X64.Semantics

open Std Std.ExtHashMap

namespace AesCtrX86

/-- The registers and memory of the AES-NI path after `b` blocks: `nr` in RAX,
the key schedule in RBX, block `b` of `src` and `dst` in RSI and RDX, the
counter `[ivlo + b, ivhi]` in X9 and the byte-reversal mask in X10; RSP, RBP,
R14 and R15 as at entry; and `MemInv c b`. -/
structure NIRegs (c : Call) (b : Nat) (s : MachineData) : Prop where
  rax : s.regs.rax.toBitVec = BitVec.ofNat 64 c.nr
  rbx : s.regs.rbx.toBitVec = c.xk
  rsi : s.regs.rsi.toBitVec = blockAddr c.src b
  rdx : s.regs.rdx.toBitVec = blockAddr c.dst b
  rsp : s.regs.rsp = c.regs.rsp
  rbp : s.regs.rbp = c.regs.rbp
  r14 : s.regs.r14 = c.regs.r14
  r15 : s.regs.r15 = c.regs.r15
  x9 : BitVec.setWidth 128 s.zmms.zmm9 = c.ivhi ++ (c.ivlo + BitVec.ofNat 64 b)
  x10 : BitVec.setWidth 128 s.zmms.zmm10 = 5233100606242806050955395731361295#128
  mem : MemInv c b s.dmem

/-! ## Bytes outside `dst` -/

/-- A byte in block `i < n` of `dst` is in `dst`. -/
theorem inR_dst_of_block {c : Call} (hc : Bufs c) {a : BitVec 64} {i : Nat}
    (hi : i < c.n) (h : InR a (blockAddr c.dst i) 16) : InR a c.dst (16 * c.n) := by
  have hfit := hc.dst_fit
  rw [inR_iff _ _ _ (by rw [blockAddr_toNat _ _ (by omega)]; omega),
    blockAddr_toNat _ _ (by omega)] at h
  rw [inR_iff _ _ _ hfit]
  omega

/-- Byte `t` of block `j < n` of `src` is in `src`. -/
theorem inR_src_block {c : Call} (hc : Bufs c) {j t : Nat} (hj : j < c.n)
    (ht : t < 16) : InR (blockAddr c.src j + BitVec.ofNat 64 t) c.src (16 * c.n) := by
  have hfit := hc.src_fit
  rw [inR_iff _ _ _ hfit, blockByte_toNat _ _ _ ht (by omega)]
  omega

/-- A byte of a source block `j` is in no destination block `i ≠ j`. -/
theorem src_not_dst_block {c : Call} (hc : Bufs c) {i j t : Nat} (hi : i < c.n)
    (hj : j < c.n) (ht : t < 16) (hij : i ≠ j) :
    ¬ InR (blockAddr c.src j + BitVec.ofNat 64 t) (blockAddr c.dst i) 16 := by
  have hfit := hc.dst_fit
  rcases hc.src_dst with h | h
  · rw [h, inR_blockByte_block _ _ _ _ ht (by omega) (by omega)]
    exact fun h' => hij h'.symm
  · exact fun hin => h _ (inR_dst_of_block hc hi hin) (inR_src_block hc hj ht)

/-- A byte of a source block `j ≥ b` is not in the first `b` blocks of `dst`. -/
theorem src_not_dst_prefix {c : Call} (hc : Bufs c) {b j t : Nat} (hbj : b ≤ j)
    (hj : j < c.n) (ht : t < 16) :
    ¬ InR (blockAddr c.src j + BitVec.ofNat 64 t) c.dst (16 * b) := by
  have hfit := hc.dst_fit
  rcases hc.src_dst with h | h
  · rw [h, inR_blockByte _ _ _ _ ht (by omega) (by omega)]
    omega
  · exact fun hin => h _ (inR_mono hin (by omega)) (inR_src_block hc hj ht)

/-! ## The loads of a group -/

/-- Round key `r` (as at entry). -/
theorem key_fact {c : Call} (hc : Bufs c) {b : Nat} {m : Mem 64}
    (hinv : MemInv c b m) (hb : b ≤ c.n) (r : Nat) (hr : r ≤ c.nr) :
    Mem.loadInt m (blockAddr c.xk r) 16 = some ((c.rk r).toNat : Int) := by
  have hfit := hc.xk_fit
  have hr14 : r ≤ 14 := by rcases hc.nr with h | h | h <;> omega
  rw [loadInt_frame hinv]
  · exact hc.keys r hr
  · intro t ht hin
    apply hc.sep_keys _ (inR_mono hin (by omega))
    rw [inR_iff _ _ _ hfit, blockByte_toNat _ _ _ ht (by omega)]
    omega

/-- Source block `j ≥ b`, after the group stored blocks `b .. j-1` of `dst`. -/
theorem src_fact {c : Call} (hc : Bufs c) {b : Nat} {m : Mem 64}
    (hinv : MemInv c b m) (j : Nat) (hbj : b ≤ j) (hj : j < c.n) (l : List (Nat × Int))
    (hl : ∀ p ∈ l, p.1 < j) :
    Mem.loadInt (stores m c.dst l) (blockAddr c.src j) 16 = some ((c.srcb j).toNat : Int) := by
  rw [loadInt_stores _ _ _ _ _ (fun p hp t ht =>
      src_not_dst_block hc (by have := hl p hp; omega) hj ht (by have := hl p hp; omega)),
    loadInt_frame hinv _ _ (fun t ht => src_not_dst_prefix hc hbj hj ht)]
  exact hc.srcs j hj

/-- Destination block `j ≥ b` reads as at entry, after the group stored blocks
`b .. j-1`. -/
theorem dst_fact {c : Call} (hc : Bufs c) {b : Nat} {m : Mem 64}
    (hinv : MemInv c b m) (j : Nat) (hbj : b ≤ j) (hj : j < c.n) (l : List (Nat × Int))
    (hl : ∀ p ∈ l, p.1 < j) :
    Mem.loadInt (stores m c.dst l) (blockAddr c.dst j) 16 =
      Mem.loadInt c.mem (blockAddr c.dst j) 16 := by
  have hfit := hc.dst_fit
  rw [loadInt_stores _ _ _ _ _ (fun p hp t ht hin => by
      have := hl p hp
      exact absurd ((inR_blockByte_block _ _ _ _ ht (by omega) (by omega)).mp hin) (by omega)),
    loadInt_frame hinv _ _ (fun t ht hin => by
      have := (inR_blockByte _ _ _ _ ht (by omega) (by omega)).mp hin
      omega)]

/-- Entry `k` of `ctrOffsets`, after any stores into `dst`. -/
theorem off_fact {c : Call} {v : Bool} (hc : Pre c v) {b : Nat} {m : Mem 64}
    (hinv : MemInv c b m) (hb : b ≤ c.n) (k : Nat) (hk : k ≤ 16) (l : List (Nat × Int))
    (hl : ∀ p ∈ l, p.1 < c.n) :
    Mem.loadInt (stores m c.dst l) (offAddr k) 16 = some (k : Int) := by
  have hbase : (0x55c940#64 : BitVec 64).toNat = 5622080 := by decide
  have h0 : (offAddr 0).toNat = 5622080 := by decide
  have hoff : ∀ t < 16, InR (offAddr k + BitVec.ofNat 64 t) (offAddr 0) 272 := by
    intro t ht
    have h1 : (offAddr k + BitVec.ofNat 64 t).toNat = 5622080 + 16 * k + t := by
      unfold offAddr
      rw [toNat_add_of_lt _ _ (by rw [toNat_add_of_lt _ _ (by rw [hbase]; omega), hbase]; omega),
        toNat_add_of_lt _ _ (by rw [hbase]; omega), hbase]
    rw [inR_iff _ _ _ (by rw [h0]; omega), h1, h0]
    omega
  rw [loadInt_stores _ _ _ _ _ (fun p hp t ht hin =>
      hc.sep_offs _ (inR_dst_of_block hc.toBufs (hl p hp) hin) (hoff t ht)),
    loadInt_frame hinv _ _ (fun t ht hin => hc.sep_offs _ (inR_mono hin (by omega)) (hoff t ht))]
  rw [hc.offs k hk]
  congr 2
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

end AesCtrX86

namespace AesCtrX86

/-! ## Helpers for the group lemmas -/

theorem memInv_zero (c : Call) : MemInv c 0 c.mem :=
  ⟨fun _ h => absurd h (by omega), fun _ _ => rfl⟩

/-- `ctr_lanes` in the form `simp` leaves it in. -/
theorem ctr_lanes' (lo hi : BitVec 64) :
    (BitVec.ofLanes 128 64 fun i =>
      if (i == 1) = true then BitVec.extractLsb' 0 64 hi
      else BitVec.lane 64 i (BitVec.setWidth 128 lo)) = hi ++ lo := by
  simpa using ctr_lanes lo hi

/-- What holds when a function returns: it is back at the return address, RET
popped it (RSP is 8 higher), RBP, R14 and R15 are as at entry, and memory is
`MemInv c c.n`: block `i < n` of `dst` holds block `i` of `src` XOR keystream
block `i`, and every other byte is as at entry. -/
structure Post (c : Call) (st : MachineState) : Prop where
  pc : st.2 = Int64.ofBitVec c.ra
  rsp : st.1.regs.rsp.toBitVec = c.rsp + 8#64
  rbp : st.1.regs.rbp = c.regs.rbp
  r14 : st.1.regs.r14 = c.regs.r14
  r15 : st.1.regs.r15 = c.regs.r15
  mem : MemInv c c.n st.1.dmem

theorem ofInt_natCast64 (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  simp

/-- The state after the last group: only the preserved registers and memory. -/
structure NIFinal (c : Call) (b : Nat) (s : MachineData) : Prop where
  rsp : s.regs.rsp = c.regs.rsp
  rbp : s.regs.rbp = c.regs.rbp
  r14 : s.regs.r14 = c.regs.r14
  r15 : s.regs.r15 = c.regs.r15
  mem : MemInv c b s.dmem

theorem NIRegs.final {c : Call} {b : Nat} {s : MachineData} (h : NIRegs c b s) :
    NIFinal c b s := ⟨h.rsp, h.rbp, h.r14, h.r15, h.mem⟩

/-- A `test` or `cmp` changes only the flags. -/
theorem niRegs_status {c : Call} {b : Nat} {s : MachineData} (h : NIRegs c b s)
    (st : StatusFlags) : NIRegs c b { s with status := st } :=
  ⟨h.rax, h.rbx, h.rsi, h.rdx, h.rsp, h.rbp, h.r14, h.r15, h.x9, h.x10, h.mem⟩

theorem memInv_store' {c : Call} (hc : Bufs c) {b b' : Nat} (hb' : b' = b + 1)
    {m : Mem 64} (hinv : MemInv c b m) (hb : b < c.n) (x : BitVec 128) (hx : x = c.out b) :
    MemInv c b' (Mem.storeInt m (blockAddr c.dst b) 16 x.toInt) :=
  hb' ▸ memInv_store hc hinv hb x hx

/-! The `test $k, %rdi` of the tail, with `r0 < 8` blocks left after the loop: its
zero flag says whether the group of `k` blocks is skipped. -/

theorem test_bit_4 : ∀ r0, r0 < 8 →
    (BitVec.ofNat 64 r0 &&& BitVec.ofNat 64 4 == BitVec.zero 64) = !decide (4 ≤ r0 % 8) := by
  decide
theorem test_bit_2 : ∀ r0, r0 < 8 →
    (BitVec.ofNat 64 r0 &&& BitVec.ofNat 64 2 == BitVec.zero 64) = !decide (2 ≤ r0 % 4) := by
  decide
theorem test_bit_1 : ∀ r0, r0 < 8 →
    (BitVec.ofNat 64 r0 &&& BitVec.ofNat 64 1 == BitVec.zero 64) = !decide (1 ≤ r0 % 2) := by
  decide

end AesCtrX86
