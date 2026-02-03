import Lake
open Lake DSL

package «forge-proofs» where
  version := "0.1.0"
  -- Require Mathlib for formal proofs
  -- moreLinkArgs := #["-L./.lake/packages/mathlib/.lake/build/lib", "-lMathlib"]

-- Main proofs library: Session, Message, Provider, FileReading invariants
lean_lib «ForgeProofs» where
  roots := #[`Forge.Proofs]
  srcDir := "Forge"

-- Bridge protocol proofs: JSON-RPC, WebSocket, State
lean_lib «BridgeProofs» where
  roots := #[`Bridge]
  srcDir := "Bridge"

@[default_target]
lean_lib «AllProofs» where
  roots := #[`Forge.Proofs, `Bridge]

-- Dependencies (uncomment when building)
-- require mathlib from git
--   "https://github.com/leanprover-community/mathlib4"

-- require std from git
--   "https://github.com/leanprover/std4" @ "main"
