/-
The VAES path works on 256-bit registers that hold two blocks, one per
128-bit lane, and loads and stores 32 bytes (two blocks) at a time. These
lemmas take such values and accesses apart into their two blocks, so that the
rest of the proof is about blocks, as on the AES-NI path.
-/
import AesCtrX86.MemLib
import AesCtrX86.Values
import AesCtrX86.Defs
import Kraken.X64.Ops.Lanes

open Std Std.ExtHashMap

namespace AesCtrX86

/-! ## Lanes -/

theorem ofLanes_256 (f : Nat → BitVec 128) : BitVec.ofLanes 256 128 f = f 1 ++ f 0 := by
  have hr : List.range 2 = [0, 1] := by decide
  simp only [BitVec.ofLanes, Nat.reduceDiv, hr, List.foldl_cons, List.foldl_nil, Nat.zero_mul,
    Nat.one_mul, BitVec.shiftLeft_zero]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_append]
  by_cases h : i < 128
  · simp [h, hi]
  · have h2 : (f 0).getLsbD i = false := BitVec.getLsbD_of_ge _ _ (by omega)
    have h3 : i - 128 < 256 := by omega
    simp [h, hi, h2, h3]

/-- A lane-wise operation on two 256-bit values works on each lane. -/
theorem map2_256 (f : BitVec 128 → BitVec 128 → BitVec 128) (a b : BitVec 256) :
    BitVec.map2 128 f a b =
      f (BitVec.lane 128 1 a) (BitVec.lane 128 1 b) ++ f (BitVec.lane 128 0 a) (BitVec.lane 128 0 b) := by
  simp only [BitVec.map2, ofLanes_256]

theorem lane1_append (x y : BitVec 128) : BitVec.lane 128 1 (x ++ y) = x := by
  unfold BitVec.lane
  rw [Nat.one_mul]
  exact BitVec.extractLsb'_append_eq_left

theorem lane0_append (x y : BitVec 128) : BitVec.lane 128 0 (x ++ y) = y := by
  unfold BitVec.lane
  rw [Nat.zero_mul]
  exact BitVec.extractLsb'_append_eq_right

theorem lane0_setWidth (x : BitVec 128) : BitVec.lane 128 0 (BitVec.setWidth 256 x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.lane, hi]
  omega

/-- A lane of a constant is a constant. -/
theorem lane_lit (i n : Nat) :
    BitVec.lane 128 i (BitVec.ofNat 256 n) = BitVec.extractLsb' (i * 128) 128 (BitVec.ofNat 256 n) :=
  rfl

theorem append_eq (x y : BitVec 128) : BitVec.append x y = x ++ y := rfl

/-- Reading back a 256-bit register write. -/
theorem setWidth_256_512 (v : BitVec 256) : BitVec.setWidth 256 (BitVec.setWidth 512 v) = v := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- Reading the low 128 bits back after a 128-bit VEX write. -/
theorem setWidth_128_512 (v : BitVec 128) : BitVec.setWidth 128 (BitVec.setWidth 512 v) = v := by
  rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]

/-- The low lane of a register read as 128 bits. -/
theorem setWidth_128_256 (x y : BitVec 128) : BitVec.setWidth 128 (x ++ y) = y :=
  BitVec.setWidth_append_eq_right

theorem ofInt_toNat256 (x : BitVec 256) : BitVec.ofInt 256 (x.toNat : Int) = x := by simp

/-! ## 32-byte loads and stores -/

theorem allSome_length {l : List (Option UInt8)} {bs : List UInt8} (h : l.allSome = some bs) :
    bs.length = l.length := by
  induction l generalizing bs with
  | nil =>
    simp only [List.allSome, List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    rfl
  | cons x l ih =>
    simp only [List.allSome, List.mapM_cons, id] at h ih
    cases x with
    | none => simp at h
    | some a =>
      cases hl : l.mapM id with
      | none => simp [hl] at h
      | some r =>
        simp only [hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        subst h
        simp [ih hl]

theorem allSome_append (l1 l2 : List (Option UInt8)) :
    (l1 ++ l2).allSome = (do let a ← l1.allSome; let b ← l2.allSome; pure (a ++ b)) := by
  simp only [List.allSome, List.mapM_append]

theorem loadBytes_add (m : Mem 64) (a : BitVec 64) (n1 n2 : Nat) :
    Mem.loadBytes m a (n1 + n2) =
      (do let l1 ← Mem.loadBytes m a n1
          let l2 ← Mem.loadBytes m (a + BitVec.ofNat 64 n1) n2
          pure (l1 ++ l2)) := by
  unfold Mem.loadBytes
  rw [List.range_add, List.map_append, allSome_append, List.map_map]
  simp only [Function.comp_def, BitVec.ofNat_add, BitVec.add_assoc]

/-- A 32-byte load is two 16-byte loads. -/
theorem loadInt_32 (m : Mem 64) (a : BitVec 64) (z0 z1 : Int)
    (h0 : Mem.loadInt m a 16 = some z0) (h1 : Mem.loadInt m (a + 16#64) 16 = some z1) :
    Mem.loadInt m a 32 = some (z0 + 2 ^ 128 * z1) := by
  unfold Mem.loadInt at *
  obtain ⟨l1, hl1, rfl⟩ := Option.map_eq_some_iff.mp h0
  obtain ⟨l2, hl2, rfl⟩ := Option.map_eq_some_iff.mp h1
  have hlen : l1.length = 16 := by
    have := allSome_length hl1
    simpa using this
  rw [show (32 : Nat) = 16 + 16 from rfl, loadBytes_add, hl1,
    show BitVec.ofNat 64 16 = 16#64 from rfl, hl2]
  simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some,
    Int.ofBytes_append, hlen]
  rfl

/-- Two blocks of `base`, read as one 32-byte value. -/
theorem loadInt_32_blk (m : Mem 64) (base : BitVec 64) (i : Nat) (x y : BitVec 128)
    (h0 : Mem.loadInt m (blockAddr base i) 16 = some (x.toNat : Int))
    (h1 : Mem.loadInt m (blockAddr base (i + 1)) 16 = some (y.toNat : Int)) :
    Mem.loadInt m (blockAddr base i) 32 = some ((y ++ x).toNat : Int) := by
  rw [loadInt_32 m _ _ _ h0 (by rw [blockAddr_add _ _ _ (by decide)]; exact h1)]
  congr 1
  have happ : (y ++ x).toNat = y.toNat * 2 ^ 128 + x.toNat := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt x.isLt, Nat.shiftLeft_eq]
  rw [happ]
  simp only [Nat.reducePow, Int.reducePow]
  omega

theorem loadInt_32_blk' (m : Mem 64) (base : BitVec 64) (i : Nat) (z0 z1 : Int)
    (h0 : Mem.loadInt m (blockAddr base i) 16 = some z0)
    (h1 : Mem.loadInt m (blockAddr base (i + 1)) 16 = some z1) :
    Mem.loadInt m (blockAddr base i) 32 = some (z0 + 2 ^ 128 * z1) :=
  loadInt_32 m _ _ _ h0 (by rw [blockAddr_add _ _ _ (by decide)]; exact h1)

theorem toBytes_add (n1 n2 : Nat) (v : Int) :
    Int.toBytes (n1 + n2) v = Int.toBytes n1 v ++ Int.toBytes n2 (v / 256 ^ n1) := by
  induction n1 generalizing v with
  | zero => simp [Int.toBytes]
  | succ n ih =>
    rw [show n + 1 + n2 = (n + n2) + 1 by omega]
    have e : v / 256 / 256 ^ n = v / 256 ^ (n + 1) := by
      rw [Int.ediv_ediv_of_nonneg (by decide), Int.pow_succ']
    simp only [Int.toBytes, ih, List.cons_append, e]

theorem toBytes_congr (n : Nat) (v w : Int) (h : v % 2 ^ (8 * n) = w % 2 ^ (8 * n)) :
    Int.toBytes n v = Int.toBytes n w := by
  rw [← Int.toBytes_emod n v, ← Int.toBytes_emod n w]
  simp only [Int.take]
  rw [h]

/-- A 32-byte store is two 16-byte stores, of the low block then the high one. -/
theorem storeInt_32 (m : Mem 64) (a : BitVec 64) (x y : BitVec 128) :
    Mem.storeInt m a 32 (y ++ x).toInt =
      Mem.storeInt (Mem.storeInt m a 16 x.toInt) (a + 16#64) 16 y.toInt := by
  have hx := x.isLt
  have hy := y.isLt
  have happ : (y ++ x).toNat = y.toNat * 2 ^ 128 + x.toNat := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt hx, Nat.shiftLeft_eq]
  have hsplit : Int.toBytes 32 (y ++ x).toInt =
      Int.toBytes 16 x.toInt ++ Int.toBytes 16 y.toInt := by
    rw [show (32 : Nat) = 16 + 16 from rfl, toBytes_add]
    congr 1
    · apply toBytes_congr
      rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
      simp only [Nat.reducePow, Nat.reduceMul] at hx hy happ ⊢
      split <;> split <;> omega
    · apply toBytes_congr
      rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
      simp only [Nat.reducePow, Nat.reduceMul] at hx hy happ ⊢
      split <;> split <;> omega
  apply ExtHashMap.ext_getElem?
  intro k
  rw [getElem?_storeInt _ _ _ _ _ (by decide), getElem?_storeInt _ _ _ _ _ (by decide),
    getElem?_storeInt _ _ _ _ _ (by decide), hsplit]
  have hd : (k - (a + 16#64)).toNat = ((k - a).toNat + (2 ^ 64 - 16)) % 2 ^ 64 := by
    have := a.isLt
    have := k.isLt
    rw [BitVec.toNat_sub, BitVec.toNat_sub, BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
    omega
  have hka := (k - a).isLt
  have e2 : InR k (a + 16#64) 16 ↔ 16 ≤ (k - a).toNat ∧ (k - a).toNat < 32 := by
    unfold InR
    rw [hd]
    simp only [Nat.reducePow, Nat.reduceSub] at hka ⊢
    omega
  by_cases h1 : (k - a).toNat < 16
  · rw [if_pos (show InR k a 32 by unfold InR; omega), if_neg (by rw [e2]; omega),
      if_pos (show InR k a 16 from h1),
      List.getElem?_append_left (by rw [Int.toBytes_length]; exact h1)]
  · by_cases h2 : (k - a).toNat < 32
    · have hd' : (k - (a + 16#64)).toNat = (k - a).toNat - 16 := by
        rw [hd]
        simp only [Nat.reducePow, Nat.reduceSub] at hka ⊢
        omega
      rw [if_pos (show InR k a 32 from h2), if_pos (by rw [e2]; omega),
        List.getElem?_append_right (by rw [Int.toBytes_length]; omega), Int.toBytes_length, hd']
    · rw [if_neg (show ¬ InR k a 32 from h2), if_neg (by rw [e2]; omega),
        if_neg (show ¬ InR k a 16 from h1)]

/-! ## The counter and the last round with the key first -/

/-- The VAES code XORs the source block into the last round key, in this order. -/
theorem out_eq' (c : Call) (j : Nat) (hj : c.ivlo.toNat + j < 2 ^ 64) :
    SimdCrypto.aesenclast.interp
      (encRounds c.rk (SimdShuf.pshufb.interp (c.ivhi ++ (c.ivlo + BitVec.ofNat 64 j))
        5233100606242806050955395731361295#128 ^^^ c.rk 0) (c.nr - 1))
      (c.rk c.nr ^^^ c.srcb j) = c.out j := by
  rw [BitVec.xor_comm (c.rk c.nr)]
  exact out_eq c j hj

end AesCtrX86
