-- | Lean4 Lakefile for Nexus Proofs
import Lake
open Lake DSL

package "nexus-proofs" where
  version := "0.1.0"

@[default_target]
lean_lib «NexusProofs» where
  roots := #[`Nexus]
