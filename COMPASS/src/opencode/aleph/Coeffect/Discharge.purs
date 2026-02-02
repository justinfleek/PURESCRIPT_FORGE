{-|
Module      : Aleph.Coeffect.Discharge
Description : Discharge proofs for coeffect verification
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Discharge Protocol

Proofs that resource requirements were satisfied:

@
  discharge : Resource → DischargeProof → Either DischargeError ()

  -- Each resource type has corresponding evidence:
  Network    → NetworkAccess
  Auth p     → AuthProof
  Container  → ContainerProof
  Filesystem → FilesystemProof
  GPU        → GPUProof
  Search     → SearchProof
  AST        → ASTProof
@

Discharge proofs form the audit trail for attestation.
-}
module Aleph.Coeffect.Discharge
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

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array

import Aleph.Coeffect.Spec (SandboxKind)

-- Forward declaration - will import from Resource
foreign import data Resource :: Type

-- ════════════════════════════════════════════════════════════════════════════
-- PROOF TYPES
-- ════════════════════════════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════════════════════════════
-- DISCHARGE PROOF
-- ════════════════════════════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════════════════════════════
-- DISCHARGE VERIFICATION
-- ════════════════════════════════════════════════════════════════════════════

-- | Verify discharge proof satisfies resource requirement
-- | Note: Implementation uses FFI to avoid circular dependency
discharge :: Resource -> DischargeProof -> Either String Unit
discharge = dischargeImpl

foreign import dischargeImpl :: Resource -> DischargeProof -> Either String Unit
