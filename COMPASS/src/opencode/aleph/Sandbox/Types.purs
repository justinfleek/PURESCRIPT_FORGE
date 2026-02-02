{-|
Module      : Aleph.Sandbox.Types
Description : Type definitions for gVisor sandbox
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Sandbox Types

Core type definitions for the gVisor container isolation layer.
This module contains sandbox kinds, policies, and container configuration.

== System F-w Encoding

@
  Kind Sandbox = Unrestricted | Network | Filesystem | GPU | Full

  -- Type constructor indexed by sandbox kind
  data Sandboxed :: Sandbox -> Type -> Type
@
-}
module Aleph.Sandbox.Types
  ( -- * Sandbox Kinds
    SandboxKind(..)
    -- * Container Configuration
  , ContainerConfig(..)
  , MountConfig(..)
  , MountType(..)
  , RootfsMode(..)
  , NetworkMode(..)
    -- * Execution Results
  , ExecOutput(..)
  , ExecMetrics(..)
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Argonaut (class EncodeJson, encodeJson)

import Aleph.Sandbox.Policy (SandboxPolicy)

-- ============================================================================
-- SANDBOX KINDS
-- ============================================================================

{-| Sandbox kind determines isolation level.

In System F-w, this would be:
@
  data SandboxKind :: Type where
    Unrestricted :: SandboxKind   -- No sandbox (DANGEROUS)
    NetworkOnly  :: SandboxKind   -- Network isolated
    FilesysOnly  :: SandboxKind   -- Filesystem isolated
    GPUPassthru  :: SandboxKind   -- GPU access, other isolated
    FullIsolate  :: SandboxKind   -- Complete isolation
@
-}
data SandboxKind
  = Unrestricted
  | NetworkOnly
  | FilesystemOnly
  | GPUPassthrough
  | FullIsolation

derive instance eqSandboxKind :: Eq SandboxKind
derive instance ordSandboxKind :: Ord SandboxKind
derive instance genericSandboxKind :: Generic SandboxKind _

instance showSandboxKind :: Show SandboxKind where
  show = genericShow

instance encodeJsonSandboxKind :: EncodeJson SandboxKind where
  encodeJson = case _ of
    Unrestricted -> encodeJson "unrestricted"
    NetworkOnly -> encodeJson "network"
    FilesystemOnly -> encodeJson "filesystem"
    GPUPassthrough -> encodeJson "gpu"
    FullIsolation -> encodeJson "full"

-- ============================================================================
-- CONTAINER CONFIGURATION
-- ============================================================================

{-| Container configuration for gVisor.

@
  record ContainerConfig where
    constructor MkConfig
    image     : String              -- OCI image reference
    command   : List String         -- Command + args
    workdir   : String              -- Working directory
    env       : List (String, String)  -- Environment variables
    mounts    : List Mount          -- Filesystem mounts
    policy    : SandboxPolicy       -- Isolation policy
    rootfs    : RootfsMode          -- Rootfs handling
@
-}
type ContainerConfig =
  { image :: String
  , command :: Array String
  , workdir :: String
  , env :: Array { key :: String, value :: String }
  , mounts :: Array MountConfig
  , policy :: SandboxPolicy
  , rootfs :: RootfsMode
  , networkMode :: NetworkMode
  }

type MountConfig =
  { source :: String
  , target :: String
  , readOnly :: Boolean
  , mountType :: MountType
  }

data MountType
  = BindMount
  | TmpfsMount
  | OverlayMount

derive instance eqMountType :: Eq MountType
derive instance genericMountType :: Generic MountType _

instance showMountType :: Show MountType where
  show = genericShow

data RootfsMode
  = ReadOnlyRootfs
  | ReadWriteRootfs
  | OverlayRootfs String  -- Base layer path

derive instance eqRootfsMode :: Eq RootfsMode
derive instance genericRootfsMode :: Generic RootfsMode _

instance showRootfsMode :: Show RootfsMode where
  show = genericShow

data NetworkMode
  = NoNetwork           -- Completely isolated
  | HostNetwork         -- Share host network (DANGEROUS)
  | BridgeNetwork       -- Private bridge
  | CustomNetwork String -- Named network

derive instance eqNetworkMode :: Eq NetworkMode
derive instance genericNetworkMode :: Generic NetworkMode _

instance showNetworkMode :: Show NetworkMode where
  show = genericShow

-- ============================================================================
-- EXECUTION RESULTS
-- ============================================================================

type ExecOutput =
  { stdout :: String
  , stderr :: String
  , exitCode :: Int
  , metrics :: ExecMetrics
  }

type ExecMetrics =
  { wallTimeMs :: Int
  , userTimeMs :: Int
  , sysTimeMs :: Int
  , maxRssMB :: Int
  , syscallCount :: Int
  }
