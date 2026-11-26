/-
The theorems, one per assembly function of `ctr_amd64.s`, stated in full.

Each says: started at the function's entry in a state where the call is as
the contract says (`Pre` in Contract.lean for `ctrBlocksBulkAsm`, `PreF` in
FLemmas.lean for master's fixed-size functions), with any other registers
and flags, every run of the program returns to the caller in a state that
satisfies `Post` (NIState.lean): `dst` holds `src` XOR the keystream of the
spec (Spec.lean), everything else in memory is as it was, and RSP, RBP, R14
and R15 are as Go needs them. `Reaches` (Reach.lean) is Kraken's "every run
eventually reaches": a run that faults or meets an instruction Kraken does
not model does not count as reaching.
-/
import AesCtrX86.VBulk
import AesCtrX86.FCorrect

namespace AesCtrX86

/-- `ctrBlocksBulkAsm(nr, xk, dst, src, n, ivlo, ivhi, vaes)`: `n ≥ 1` blocks,
on the VAES path (`vaes`) or the AES-NI path, provided the low 64 bits of the
counter do not wrap within them. -/
theorem ctrBlocksBulkAsm_correct (c : Call) (vaes : Bool) (hc : Pre c vaes)
    (hrsp : c.regs.rsp.toBitVec = c.rsp) (zmms : RegZmms) (flags : StatusFlags) :
    Reaches exe (Post c) (⟨c.regs, zmms, flags, c.mem⟩, entry_bulk) :=
  bulk_correct c vaes hc hrsp zmms flags

/-- `ctrBlocks1Asm(nr, xk, dst, src, ivlo, ivhi)`: one block. -/
theorem ctrBlocks1Asm_correct (c : Call) (hc : PreF c) (hn : c.n = 1)
    (hrsp : c.regs.rsp.toBitVec = c.rsp) (zmms : RegZmms) (flags : StatusFlags) :
    Reaches exe (Post c) (⟨c.regs, zmms, flags, c.mem⟩, entry_ctr1) :=
  ctr1_correct c hc hn hrsp zmms flags

/-- `ctrBlocks2Asm`: two blocks; the counter may wrap. -/
theorem ctrBlocks2Asm_correct (c : Call) (hc : PreF c) (hn : c.n = 2)
    (hrsp : c.regs.rsp.toBitVec = c.rsp) (zmms : RegZmms) (flags : StatusFlags) :
    Reaches exe (Post c) (⟨c.regs, zmms, flags, c.mem⟩, entry_ctr2) :=
  ctr2_correct c hc hn hrsp zmms flags

/-- `ctrBlocks4Asm`: four blocks; the counter may wrap. -/
theorem ctrBlocks4Asm_correct (c : Call) (hc : PreF c) (hn : c.n = 4)
    (hrsp : c.regs.rsp.toBitVec = c.rsp) (zmms : RegZmms) (flags : StatusFlags) :
    Reaches exe (Post c) (⟨c.regs, zmms, flags, c.mem⟩, entry_ctr4) :=
  ctr4_correct c hc hn hrsp zmms flags

/-- `ctrBlocks8Asm`: eight blocks; the counter may wrap. -/
theorem ctrBlocks8Asm_correct (c : Call) (hc : PreF c) (hn : c.n = 8)
    (hrsp : c.regs.rsp.toBitVec = c.rsp) (zmms : RegZmms) (flags : StatusFlags) :
    Reaches exe (Post c) (⟨c.regs, zmms, flags, c.mem⟩, entry_ctr8) :=
  ctr8_correct c hc hn hrsp zmms flags

end AesCtrX86
