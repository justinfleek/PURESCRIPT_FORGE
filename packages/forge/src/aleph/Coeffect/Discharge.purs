{-|
Module      : Forge.Aleph.Coeffect.Discharge
Description : Discharge proofs for coeffect verification
= Discharge Protocol

Proofs that resource requirements were satisfied:

@
  discharge : Resource -> DischargeProof -> Either DischargeError ()

  -- Each resource type has corresponding evidence:
  Network    -> NetworkAccess
  Auth p     -> AuthProof
  Container  -> ContainerProof
  Filesystem -> FilesystemProof
  GPU        -> GPUProof
  Search     -> SearchProof
  AST        -> ASTProof
@

Discharge proofs form the audit trail for attestation.
-}
module Forge.Aleph.Coeffect.Discharge
  ( -- * Proof Types
    DischargeProof(..)
  , NetworkAccess(..)
  , AuthProof(..)
  , SandboxConfig(..)
  , ContainerProof(..)
  , FilesystemProof(..)
  , GPUProof(..)
  , SearchProof(..)
  , ASTProof(..)
    -- * Operations
  , discharge
  , emptyProof
  ) where

import Prelude

import Data.Maybe (Maybe(..), isJust)
import Data.Either (Either(..))
import Data.Array as Array

import Forge.Aleph.Coeffect.Spec (SandboxKind)
import Forge.Aleph.Coeffect.Resource (Resource(..), flatten)

-- ============================================================================
-- PROOF TYPES
-- ============================================================================

type NetworkAccess =
  { url :: String
  , responseHash :: String
  , timestamp :: Number
  , statusCode :: Int
  , bytesTransferred :: Int
  }

type AuthProof =
  { provider :: String
  , credentialHash :: String
  , scopes :: Array String
  , expiresAt :: Maybe Number
  }

type SandboxConfig =
  { kind :: SandboxKind
  , isolated :: Boolean
  , capabilities :: Array String
  }

type ContainerProof =
  { containerId :: String
  , image :: String
  , exitCode :: Int
  , startTime :: Number
  , endTime :: Number
  , memoryUsedMB :: Int
  , cpuTimeMs :: Int
  , syscallsBlocked :: Int
  }

type FilesystemProof =
  { path :: String
  , operation :: String
  , contentHash :: Maybe String
  , timestamp :: Number
  , bytesAccessed :: Int
  }

type GPUProof =
  { deviceId :: Int
  , deviceName :: String
  , kernelName :: String
  , executionTimeMs :: Number
  , memoryUsedMB :: Int
  }

type SearchProof =
  { backend :: String
  , queryHash :: String
  , resultCount :: Int
  , searchTimeMs :: Int
  , timestamp :: Number
  }

type ASTProof =
  { language :: String
  , filePath :: String
  , parseSuccess :: Boolean
  , nodeCount :: Int
  , errorCount :: Int
  }

-- ============================================================================
-- DISCHARGE PROOF
-- ============================================================================

type DischargeProof =
  { network :: Array NetworkAccess
  , auth :: Array AuthProof
  , sandbox :: Maybe SandboxConfig
  , container :: Array ContainerProof
  , filesystem :: Array FilesystemProof
  , gpu :: Array GPUProof
  , search :: Array SearchProof
  , ast :: Array ASTProof
  }

emptyProof :: DischargeProof
emptyProof =
  { network: []
  , auth: []
  , sandbox: Nothing
  , container: []
  , filesystem: []
  , gpu: []
  , search: []
  , ast: []
  }

-- ============================================================================
-- DISCHARGE VERIFICATION
-- ============================================================================

-- | Verify discharge proof satisfies resource requirement
discharge :: Resource -> DischargeProof -> Either String Unit
discharge resource proof =
  let atoms = flatten resource
  in verifyAll atoms proof

verifyAll :: Array Resource -> DischargeProof -> Either String Unit
verifyAll atoms proof =
  case Array.uncons atoms of
    Nothing -> Right unit
    Just { head: atom, tail: rest } ->
      case verifyAtom atom proof of
        Left err -> Left err
        Right _ -> verifyAll rest proof

verifyAtom :: Resource -> DischargeProof -> Either String Unit
verifyAtom resource proof = case resource of
  Pure -> Right unit
  Network ->
    if Array.null proof.network
    then Left "Network access required but no network proof provided"
    else Right unit
  Auth _ ->
    if Array.null proof.auth
    then Left "Authentication required but no auth proof provided"
    else Right unit
  Sandbox _ ->
    if not (isJust proof.sandbox)
    then Left "Sandbox required but no sandbox proof provided"
    else Right unit
  Container _ ->
    if Array.null proof.container
    then Left "Container required but no container proof provided"
    else Right unit
  Filesystem _ ->
    if Array.null proof.filesystem
    then Left "Filesystem access required but no filesystem proof provided"
    else Right unit
  GPU _ ->
    if Array.null proof.gpu
    then Left "GPU access required but no GPU proof provided"
    else Right unit
  Search _ ->
    if Array.null proof.search
    then Left "Search access required but no search proof provided"
    else Right unit
  AST _ ->
    if Array.null proof.ast
    then Left "AST parser required but no AST proof provided"
    else Right unit
  Both r1 r2 ->
    case discharge r1 proof of
      Left err -> Left err
      Right _ -> discharge r2 proof
