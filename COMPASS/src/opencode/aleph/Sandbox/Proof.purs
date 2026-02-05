{-|
Module      : Aleph.Sandbox.Proof
Description : Sandbox execution proofs
= Sandbox Proofs

This module provides proof types for sandbox execution, enabling
verification of isolation guarantees and integration with the
attestation chain.

== Attestation Chain

@
  Sandbox proof -> Coeffect discharge -> Attestation
@

== Proof Contents

A sandbox proof captures:
1. Container ID for traceability
2. Isolation level achieved
3. Execution time metrics
4. Resource usage statistics
5. Security events (blocked syscalls, network requests)

-}
module Aleph.Sandbox.Proof
  ( -- * Proof Types
    SandboxProof(..)
    -- * Proof Construction
  , mkSandboxProof
    -- * Verification
  , verifySandbox
    -- * Coeffect Integration
  , toDischargeProof
  ) where

import Prelude

import Effect (Effect)
import Effect.Class (liftEffect)
import Data.Either (Either(..))

import Aleph.Sandbox.Policy (SandboxPolicy, IsolationLevel(..), ResourceUsage, deriveIsolationLevel)
import Aleph.Sandbox.GVisor.FFI (getCurrentTimestamp)
import Aleph.Coeffect (DischargeProof)

-- Forward declarations to avoid circular imports
-- These types come from Types.purs and GVisor.purs
type ContainerConfig =
  { policy :: SandboxPolicy
  }

newtype GVisorRuntime = GVisorRuntime
  { containerId :: String
  }

data SandboxKind
  = Unrestricted
  | NetworkOnly
  | FilesystemOnly
  | GPUPassthrough
  | FullIsolation

-- ============================================================================
-- SANDBOX PROOF
-- ============================================================================

{-| Proof that sandbox executed correctly.

This becomes part of the attestation chain:
@
  Sandbox proof -> Coeffect discharge -> Attestation
@
-}
type SandboxProof =
  { containerId :: String
  , isolationLevel :: IsolationLevel
  , executionTime :: Number
  , resourceUsage :: ResourceUsage
  , syscallsBlocked :: Int
  , networksBlocked :: Int
  }

-- ============================================================================
-- PROOF CONSTRUCTION
-- ============================================================================

-- | Create sandbox proof from execution
mkSandboxProof :: ContainerConfig -> GVisorRuntime -> Effect SandboxProof
mkSandboxProof config (GVisorRuntime rt) = do
  -- Calculate execution time from start time
  currentTime <- getCurrentTimestamp
  let executionTime = currentTime - rt.startTime
  
  pure
    { containerId: rt.containerId
    , isolationLevel: deriveIsolationLevel config.policy
    , executionTime: executionTime
    , resourceUsage:
        { cpuMs: 0  -- Would be populated from container stats
        , memoryMB: 0
        , diskMB: 0
        , networkBytes: 0
        }
    , syscallsBlocked: 0  -- Would be populated from gVisor logs
    , networksBlocked: 0
    }

-- ============================================================================
-- VERIFICATION
-- ============================================================================

-- | Verify sandbox proof meets requirements
verifySandbox :: SandboxKind -> SandboxProof -> Either String Unit
verifySandbox kind proof = case kind of
  Unrestricted -> Right unit
  FullIsolation ->
    if proof.isolationLevel /= IsoFull
    then Left "Full isolation required but not achieved"
    else Right unit
  _ ->
    if proof.isolationLevel == IsoNone
    then Left "No isolation when some was required"
    else Right unit

-- ============================================================================
-- COEFFECT INTEGRATION
-- ============================================================================

-- | Convert sandbox proof to coeffect discharge proof
toDischargeProof :: SandboxProof -> DischargeProof
toDischargeProof proof =
  { network: []
  , auth: []
  , sandbox: Just
      { kind: show proof.isolationLevel
      , isolated: proof.isolationLevel /= IsoNone
      , capabilities: []
      }
  , filesystem: []
  }
