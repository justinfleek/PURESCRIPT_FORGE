import Lake
open Lake DSL

package «forge-proofs» where
  version := "0.1.0"

lean_lib «ForgeProofs» where
  roots := #[`Forge.Proofs]

@[default_target]
lean_lib «ForgeProofsLib» where
  roots := #[`Forge.Proofs]
