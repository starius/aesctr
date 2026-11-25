/-
Composing the loop: n iterations of the group lemma and the back edge.
-/
import AesCtr.Loop


namespace AesCtr

theorem ofNat64_sub_one (k : Nat) (hk : 1 ≤ k) (hk' : k < 2 ^ 64) :
    BitVec.ofNat 64 k - 1#64 = BitVec.ofNat 64 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hk', Nat.mod_eq_of_lt (show k - 1 < 2 ^ 64 by omega)]
  omega

theorem ofNat64_eq_zero_iff (k : Nat) (hk : k < 2 ^ 64) : BitVec.ofNat 64 k = 0#64 ↔ k = 0 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this
    simpa using this
  · intro h; subst h; rfl

/-- `n` iterations of the loop: from the loop entry (after the `CBZ`), with the
group lemma and the back-edge lemma of one key size, the loop ends at its tail
with `12 * n` blocks done. -/
theorem loop_compose {L : Layout} {s0 : ArmState} {c : Call} (n : Nat) (hn : n < 2 ^ 64)
    (B : Nat) (LOOP TAIL SUB : BitVec 64)
    (hgroup : ∀ (s : ArmState) (m : Nat), LoopInv L s0 c m s → r .PC s = LOOP →
      m + 12 ≤ c.nblocks → GroupPost L s0 c (m + 12) SUB (r (.GPR 13#5) s) (run B s))
    (hback : ∀ (s : ArmState) (m : Nat) (x : BitVec 64), GroupPost L s0 c m SUB x s →
      GroupPost L s0 c m (if x - 1#64 = 0#64 then TAIL else LOOP) (x - 1#64) (run 2 s))
    (hfit : 12 * n ≤ c.nblocks) (s : ArmState)
    (h0 : GroupPost L s0 c 0 (if BitVec.ofNat 64 n = 0#64 then TAIL else LOOP) (BitVec.ofNat 64 n) s) :
    GroupPost L s0 c (12 * n) TAIL 0#64 (run (n * (B + 2)) s) := by
  let P : Nat → ArmState → Prop := fun i s =>
    GroupPost L s0 c (12 * i) (if i < n then LOOP else TAIL) (BitVec.ofNat 64 (n - i)) s
  have hP0 : P 0 s := by
    simp only [P, Nat.mul_zero, Nat.sub_zero]
    have e : (BitVec.ofNat 64 n = 0#64) ↔ ¬ (0 < n) := by rw [ofNat64_eq_zero_iff n hn]; omega
    by_cases hn0 : 0 < n
    · rw [if_pos hn0]; have := h0; rw [if_neg (by rw [e]; exact fun h => h hn0)] at this; exact this
    · rw [if_neg hn0]; have := h0; rw [if_pos (by rw [e]; exact hn0)] at this; exact this
  have hstep : ∀ i s, i < n → P i s → P (i + 1) (run (B + 2) s) := by
    intro i s hi hPi
    simp only [P] at hPi ⊢
    rw [if_pos hi] at hPi
    have hg := hgroup s (12 * i) hPi.inv hPi.pc (by omega)
    rw [hPi.x13] at hg
    have hb := hback _ _ _ hg
    rw [run_plus]
    rw [ofNat64_sub_one (n - i) (by omega) (by omega)] at hb
    have e1 : 12 * i + 12 = 12 * (i + 1) := by omega
    have e2 : n - i - 1 = n - (i + 1) := by omega
    rw [e1, e2] at hb
    have e3 : (BitVec.ofNat 64 (n - (i + 1)) = 0#64) ↔ ¬ (i + 1 < n) := by
      rw [ofNat64_eq_zero_iff _ (by omega)]; omega
    by_cases h' : i + 1 < n
    · rw [if_pos h']; rw [if_neg (by rw [e3]; exact fun h => h h')] at hb; exact hb
    · rw [if_neg h']; rw [if_pos (by rw [e3]; exact h')] at hb; exact hb
  have := run_iterate (P := P) (B + 2) n hstep n s (Nat.le_refl n) hP0
  simp only [P, Nat.lt_irrefl, if_false, Nat.sub_self] at this
  exact this

theorem run_one (s : ArmState) : run 1 s = stepi s := rfl
theorem run_two (s : ArmState) : run 2 s = stepi (stepi s) := rfl

/-- Writing the program counter keeps a group's conclusion, at the new program counter. -/
theorem gp_pc {L : Layout} {s0 s : ArmState} {c : Call} {m : Nat} {pc x : BitVec 64}
    (pc' : BitVec 64) (hg : GroupPost L s0 c m pc x s) :
    GroupPost L s0 c m pc' x (w .PC pc' s) :=
  ⟨hg.inv.w_other _ _ (Or.inl rfl), r_of_w_same, by rw [r_of_w_different (by decide)]; exact hg.x13⟩

end AesCtr
