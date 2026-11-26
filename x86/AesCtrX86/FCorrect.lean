/-
Master's fixed-size functions are correct: called as `PreF` says, with any
counter (it may wrap: they step all 128 bits of it), `ctrBlocks<n>Asm`
returns with blocks `0 .. n-1` of `dst` holding `src` XOR the keystream, and
everything else the caller can see as it was (`Post`).
-/
import AesCtrX86.FRuns

namespace AesCtrX86

theorem ctr1_correct (c : Call) (hc : PreF c) (hn : c.n = 1)
    (hrsp : c.regs.rsp.toBitVec = c.rsp) (zmms : RegZmms) (flags : StatusFlags) :
    Reaches exe (Post c) (⟨c.regs, zmms, flags, c.mem⟩, entry_ctr1) := by
  apply reaches_of_runs
  rcases hc.nr with hnr | hnr | hnr
  · exact f1_10 c hc hn hnr hrsp zmms flags
  · exact f1_12 c hc hn hnr hrsp zmms flags
  · exact f1_14 c hc hn hnr hrsp zmms flags

theorem ctr2_correct (c : Call) (hc : PreF c) (hn : c.n = 2)
    (hrsp : c.regs.rsp.toBitVec = c.rsp) (zmms : RegZmms) (flags : StatusFlags) :
    Reaches exe (Post c) (⟨c.regs, zmms, flags, c.mem⟩, entry_ctr2) := by
  apply reaches_of_runs
  rcases hc.nr with hnr | hnr | hnr
  · exact f2_10 c hc hn hnr hrsp zmms flags
  · exact f2_12 c hc hn hnr hrsp zmms flags
  · exact f2_14 c hc hn hnr hrsp zmms flags

theorem ctr4_correct (c : Call) (hc : PreF c) (hn : c.n = 4)
    (hrsp : c.regs.rsp.toBitVec = c.rsp) (zmms : RegZmms) (flags : StatusFlags) :
    Reaches exe (Post c) (⟨c.regs, zmms, flags, c.mem⟩, entry_ctr4) := by
  apply reaches_of_runs
  rcases hc.nr with hnr | hnr | hnr
  · exact f4_10 c hc hn hnr hrsp zmms flags
  · exact f4_12 c hc hn hnr hrsp zmms flags
  · exact f4_14 c hc hn hnr hrsp zmms flags

theorem ctr8_correct (c : Call) (hc : PreF c) (hn : c.n = 8)
    (hrsp : c.regs.rsp.toBitVec = c.rsp) (zmms : RegZmms) (flags : StatusFlags) :
    Reaches exe (Post c) (⟨c.regs, zmms, flags, c.mem⟩, entry_ctr8) := by
  apply reaches_of_runs
  by_cases hw : 18446744073709551616 ≤ 7 + (lo64 (c.ivhi ++ c.ivlo)).toNat
  · rcases hc.nr with hnr | hnr | hnr
    · exact f8_10_slow c hc hn hnr hrsp zmms flags hw
    · exact f8_12_slow c hc hn hnr hrsp zmms flags hw
    · exact f8_14_slow c hc hn hnr hrsp zmms flags hw
  · rcases hc.nr with hnr | hnr | hnr
    · exact f8_10_fast c hc hn hnr hrsp zmms flags hw
    · exact f8_12_fast c hc hn hnr hrsp zmms flags hw
    · exact f8_14_fast c hc hn hnr hrsp zmms flags hw

end AesCtrX86
