/-
The loop invariant for the bulk function

  ctrBlocksAsm(nr int, xk *[60]uint32, dst, src *byte, n, r int, ivlo, ivhi uint64)

which XORs `G * n + r` blocks of keystream into `dst`: `n` groups of `G` blocks
in a loop, then `r < G` blocks in 8/4/2/1-block steps. It keeps the round keys
in vector registers and the counter in a vector register as `lo ++ hi` (lane
D[1] is the low half), and never carries into the high half (the caller splits
calls so the low half does not wrap).
-/
import AesCtr.Spec
import AesCtr.ProofLib
import Arm.Exec

namespace AesCtr

open BitVec

/-- The call of the bulk function in state `s` (arguments at `sp + 8 ...`). -/
def callBulk (G : Nat) (s : ArmState) : Call :=
  { nr := (arg s 0).toNat, xk := arg s 1, dst := arg s 2, src := arg s 3,
    nblocks := G * (arg s 4).toNat + (arg s 5).toNat, ivlo := arg s 6, ivhi := arg s 7 }

/-- Where the bulk function keeps things. Round key `k` of `nr` rounds is in
`keyReg nr k = keyEnd - nr + k`; the counter is in `ctr`; the increments
`1 ++ 0` and `2 ++ 0` are in `one` and `two`. -/
structure Layout where
  prog : Program
  G : Nat
  keyEnd : Nat
  ctr : BitVec 5
  one : BitVec 5
  two : BitVec 5

def Layout.keyReg (L : Layout) (nr k : Nat) : BitVec 5 := BitVec.ofNat 5 (L.keyEnd - nr + k)

/-- The state of the bulk function after `m` blocks, at any point between
groups. `c` is the call; `s0` the state at entry. -/
structure LoopInv (L : Layout) (s0 : ArmState) (c : Call) (m : Nat) (s : ArmState) : Prop where
  program : s.program = L.prog
  err : r .ERR s = .None
  sp_aligned : CheckSPAlignment s
  sp : r (.GPR 31#5) s = r (.GPR 31#5) s0
  x18 : r (.GPR 18#5) s = r (.GPR 18#5) s0
  x28 : r (.GPR 28#5) s = r (.GPR 28#5) s0
  x29 : r (.GPR 29#5) s = r (.GPR 29#5) s0
  x30 : r (.GPR 30#5) s = r (.GPR 30#5) s0
  keys : ∀ k, k ≤ c.nr → r (.SFP (L.keyReg c.nr k)) s = block s0 c.xk k
  one : r (.SFP L.one) s = 1#64 ++ 0#64
  two : r (.SFP L.two) s = 2#64 ++ 0#64
  ctr : r (.SFP L.ctr) s = (c.ivlo + BitVec.ofNat 64 m) ++ c.ivhi
  srcp : r (.GPR 12#5) s = c.src + BitVec.ofNat 64 (16 * m)
  dstp : r (.GPR 11#5) s = c.dst + BitVec.ofNat 64 (16 * m)
  rem : r (.GPR 15#5) s = arg s0 5
  done : ∀ j < m, block s c.dst j = block s0 c.src j ^^^ keystream c.nr (block s0 c.xk) c.ivhi c.ivlo j
  frame : ∀ (a : BitVec 64) (k : Nat), mem_separate' a k c.dst (16 * m) →
    read_mem_bytes k a s = read_mem_bytes k a s0

/-- Iterating a step that preserves an indexed invariant. -/
theorem run_iterate {P : Nat → ArmState → Prop} (B n : Nat)
    (step : ∀ i s, i < n → P i s → P (i + 1) (run B s)) :
    ∀ i s, i ≤ n → P 0 s → P i (run (i * B) s) := by
  intro i
  induction i with
  | zero => intro s _ h; simpa [run] using h
  | succ i ih =>
    intro s hi h
    have := step i (run (i * B) s) (by omega) (ih s (by omega) h)
    rw [Nat.succ_mul, run_plus]
    exact this

end AesCtr

namespace AesCtr

/-- The conclusion of a group lemma: the invariant after `m` blocks, the
program counter, and x13 (the group count, which groups leave alone). A
structure, so that `sym_n`'s final `simp` leaves the goal's shape alone. -/
structure GroupPost (L : Layout) (s0 : ArmState) (c : Call) (m : Nat) (pc x13 : BitVec 64)
    (s : ArmState) : Prop where
  inv : LoopInv L s0 c m s
  pc : r .PC s = pc
  x13 : r (.GPR 13#5) s = x13

end AesCtr

namespace AesCtr

/-- Writing the program counter, the group count x13, or the scratch register
x16 keeps the invariant: it does not mention them. -/
theorem LoopInv.w_other {L : Layout} {s0 : ArmState} {c : Call} {m : Nat} {s : ArmState}
    (h : LoopInv L s0 c m s) (f : StateField) (v : state_value f)
    (hf : f = .PC ∨ f = .GPR 13#5 ∨ f = .GPR 16#5) : LoopInv L s0 c m (w f v s) := by
  obtain ⟨hp, he, hsa, hsp, h18, h28, h29, h30, hk, h1, h2, hc, hs, hd, hr, hdone, hfr⟩ := h
  have ne : ∀ g : StateField, (g = .ERR ∨ (∃ i, g = .GPR i ∧ i ≠ 13#5 ∧ i ≠ 16#5) ∨ (∃ i, g = .SFP i)) →
      g ≠ f := by
    intro g hg heq
    subst heq
    rcases hf with rfl | rfl | rfl <;> rcases hg with h | ⟨i, h, hi1, hi2⟩ | ⟨i, h⟩ <;>
      cases h <;> first | exact hi1 rfl | exact hi2 rfl
  have rw' : ∀ g, (g = .ERR ∨ (∃ i, g = .GPR i ∧ i ≠ 13#5 ∧ i ≠ 16#5) ∨ (∃ i, g = .SFP i)) →
      r g (w f v s) = r g s := fun g hg => r_of_w_different (ne g hg)
  have gpr : ∀ i : BitVec 5, i ≠ 13#5 → i ≠ 16#5 → r (.GPR i) (w f v s) = r (.GPR i) s :=
    fun i h1 h2 => rw' _ (Or.inr (Or.inl ⟨i, rfl, h1, h2⟩))
  have sfp : ∀ i : BitVec 5, r (.SFP i) (w f v s) = r (.SFP i) s :=
    fun i => rw' _ (Or.inr (Or.inr ⟨i, rfl⟩))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [w_program]; exact hp
  · rw [rw' _ (Or.inl rfl)]; exact he
  · simp only [CheckSPAlignment, read_gpr]
    rw [gpr 31#5 (by decide) (by decide)]; exact hsa
  · rw [gpr 31#5 (by decide) (by decide)]; exact hsp
  · rw [gpr 18#5 (by decide) (by decide)]; exact h18
  · rw [gpr 28#5 (by decide) (by decide)]; exact h28
  · rw [gpr 29#5 (by decide) (by decide)]; exact h29
  · rw [gpr 30#5 (by decide) (by decide)]; exact h30
  · intro k hk'; rw [sfp]; exact hk k hk'
  · rw [sfp]; exact h1
  · rw [sfp]; exact h2
  · rw [sfp]; exact hc
  · rw [gpr 12#5 (by decide) (by decide)]; exact hs
  · rw [gpr 11#5 (by decide) (by decide)]; exact hd
  · rw [gpr 15#5 (by decide) (by decide)]; exact hr
  · intro j hj; simp only [block, read_mem_bytes_of_w]; exact hdone j hj
  · intro a k hk'; rw [read_mem_bytes_of_w]; exact hfr a k hk'

end AesCtr
