/-
Loads after stores in Kraken's byte memory (`Mem 64`, a map from addresses to
bytes): a load sees the bytes of the last store that covers them, or else the
bytes from before. A 16-byte block holding `x` is the fact
`Mem.loadInt m a 16 = some x.toNat`.
-/
import Kraken.Mem
import Kraken.ToBytes
import Std.Data.ExtHashMap.Lemmas

open Std Std.ExtHashMap

namespace AesCtrX86

/-- Byte `k` is one of the `n` bytes `a, a + 1, ..., a + n - 1` (modulo 2^64). -/
def InR (k a : BitVec 64) (n : Nat) : Prop := (k - a).toNat < n

instance (k a : BitVec 64) (n : Nat) : Decidable (InR k a n) :=
  inferInstanceAs (Decidable ((k - a).toNat < n))

theorem getElem?_storeBytes (m : Mem 64) (a : BitVec 64) (bs : List UInt8) (k : BitVec 64)
    (hl : bs.length ≤ 2 ^ 64) :
    (Mem.storeBytes m a bs)[k]? = if InR k a bs.length then bs[(k - a).toNat]? else m[k]? := by
  unfold Mem.storeBytes
  rw [show m.union (bs.At a) = m ∪ bs.At a from rfl, getElem?_union, get?_At bs a k hl]
  by_cases h : InR k a bs.length
  · rw [if_pos h, List.getElem?_eq_getElem h, Option.some_or]
  · rw [if_neg h, List.getElem?_eq_none (Nat.le_of_not_lt h), Option.none_or]

theorem getElem?_storeInt (m : Mem 64) (a : BitVec 64) (n : Nat) (v : Int) (k : BitVec 64)
    (hn : n ≤ 2 ^ 64) :
    (Mem.storeInt m a n v)[k]? = if InR k a n then (Int.toBytes n v)[(k - a).toNat]? else m[k]? := by
  unfold Mem.storeInt
  rw [getElem?_storeBytes _ _ _ _ (by rw [Int.toBytes_length]; exact hn), Int.toBytes_length]

/-- A store leaves the bytes outside its range alone. -/
theorem getElem?_storeInt_of_not (m : Mem 64) (a : BitVec 64) (n : Nat) (v : Int) (k : BitVec 64)
    (hn : n ≤ 2 ^ 64) (h : ¬ InR k a n) : (Mem.storeInt m a n v)[k]? = m[k]? := by
  rw [getElem?_storeInt _ _ _ _ _ hn]
  simp [h]

theorem loadBytes_congr (m1 m2 : Mem 64) (a : BitVec 64) (n : Nat)
    (h : ∀ i < n, m1[a + BitVec.ofNat 64 i]? = m2[a + BitVec.ofNat 64 i]?) :
    Mem.loadBytes m1 a n = Mem.loadBytes m2 a n := by
  unfold Mem.loadBytes
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [List.mem_range] at hi
  simpa [get?_eq_getElem?] using h i hi

theorem loadInt_congr (m1 m2 : Mem 64) (a : BitVec 64) (n : Nat)
    (h : ∀ i < n, m1[a + BitVec.ofNat 64 i]? = m2[a + BitVec.ofNat 64 i]?) :
    Mem.loadInt m1 a n = Mem.loadInt m2 a n := by
  unfold Mem.loadInt
  rw [loadBytes_congr m1 m2 a n h]

/-- A load that does not overlap a store sees the memory from before it. -/
theorem loadInt_storeInt_other (m : Mem 64) (a : BitVec 64) (n : Nat) (v : Int) (b : BitVec 64)
    (k : Nat) (hn : n ≤ 2 ^ 64) (h : ∀ i < k, ¬ InR (b + BitVec.ofNat 64 i) a n) :
    Mem.loadInt (Mem.storeInt m a n v) b k = Mem.loadInt m b k := by
  apply loadInt_congr
  intro i hi
  exact getElem?_storeInt_of_not _ _ _ _ _ hn (h i hi)

theorem allSome_map_some (bs : List UInt8) : (bs.map some).allSome = some bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.allSome, List.map_cons, List.mapM_cons, id] at ih ⊢
    simp [ih]

theorem loadBytes_eq_some (m : Mem 64) (a : BitVec 64) (bs : List UInt8)
    (h : ∀ i < bs.length, m[a + BitVec.ofNat 64 i]? = bs[i]?) :
    Mem.loadBytes m a bs.length = some bs := by
  unfold Mem.loadBytes
  have : (List.range bs.length).map (fun i => m.get? (a + BitVec.ofNat 64 i)) = bs.map some := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, get?_eq_getElem?]
    rw [h i (by simpa using h2), List.getElem?_eq_getElem (by simpa using h2)]
  rw [this, allSome_map_some]

/-- A load of exactly the bytes of a store sees the stored value. -/
theorem loadInt_storeInt_self (m : Mem 64) (a : BitVec 64) (n : Nat) (v : Int)
    (hn : n < 2 ^ 64) :
    Mem.loadInt (Mem.storeInt m a n v) a n = some (Int.ofBytes (Int.toBytes n v)) := by
  unfold Mem.loadInt
  have := loadBytes_eq_some (Mem.storeInt m a n v) a (Int.toBytes n v) (by
    intro i hi
    rw [Int.toBytes_length] at hi
    have hi' : (a + BitVec.ofNat 64 i - a).toNat = i := by
      rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hin : InR (a + BitVec.ofNat 64 i) a n := by unfold InR; omega
    rw [getElem?_storeInt _ _ _ _ _ (by omega)]
    simp [hin, hi'])
  rw [Int.toBytes_length] at this
  rw [this]
  rfl

/-- The bytes of a 128-bit value read back as its unsigned value. -/
theorem ofBytes_toBytes_toInt (x : BitVec 128) :
    Int.ofBytes (Int.toBytes 16 x.toInt) = (x.toNat : Int) := by
  have h1 := BitVec.ofInt_ofBytes_toBytes 128 16 rfl x
  have h2 := Int.ofBytes_ge_zero (Int.toBytes 16 x.toInt)
  have h3 := Int.ofBytes_lt (Int.toBytes 16 x.toInt)
  rw [Int.toBytes_length] at h3
  generalize Int.ofBytes (Int.toBytes 16 x.toInt) = z at h1 h2 h3
  subst h1
  rw [BitVec.toNat_ofInt]
  have h256 : (256 : Int) ^ 16 = ((2 ^ 128 : Nat) : Int) := by decide
  rw [h256] at h3
  have : z % ((2 ^ 128 : Nat) : Int) = z := Int.emod_eq_of_lt h2 h3
  rw [this]
  omega

/-- Storing the 128-bit `x` and loading it back. -/
theorem loadInt_store128_self (m : Mem 64) (a : BitVec 64) (x : BitVec 128) :
    Mem.loadInt (Mem.storeInt m a 16 x.toInt) a 16 = some (x.toNat : Int) := by
  rw [loadInt_storeInt_self _ _ _ _ (by decide), ofBytes_toBytes_toInt]

end AesCtrX86
