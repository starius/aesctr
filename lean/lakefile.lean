import Lake
open Lake DSL

/-- Machine-code proofs about Go's arm64 AES-CTR assembly, in the LNSym model. -/
package «aesctr» where
  leanOptions := #[⟨`autoImplicit, false⟩]

-- LNSym pinned by the flake (`LNSYM_SRC`); `scripts/setup-vendor.sh` puts a
-- writable copy at ../vendor/LNSym, where Lake builds it.
require lnsym from "../vendor/LNSym"

@[default_target]
lean_lib AesCtr
