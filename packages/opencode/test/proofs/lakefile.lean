import Lake
open Lake DSL

package «opencode-proofs» where
  version := "0.1.0"

lean_lib «OpencodeProofs» where
  roots := #[`Opencode.Proofs]

@[default_target]
lean_lib «OpencodeProofsLib» where
  roots := #[`Opencode.Proofs]
