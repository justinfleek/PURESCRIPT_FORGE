{-|
Module      : Forge.Aleph.Sandbox.GVisor.FFI
Description : Foreign function interface for gVisor runsc
= gVisor FFI

Foreign function interface for interacting with gVisor's runsc binary.
All functions are async and return Aff for proper error handling.

Note: RuntimeConfig, Platform, and NetworkConfig are defined here
(rather than in GVisor.purs) to avoid circular module dependencies.
-}
module Forge.Aleph.Sandbox.GVisor.FFI
  ( -- * Container Lifecycle
    createContainer
  , startContainer
  , execInContainer
  , killContainer
  , deleteContainer
    -- * Container Info
  , listContainers
  , getContainerStatus
  , getContainerPid
    -- * Utilities
  , getCurrentTimestamp
    -- * Types
  , ContainerId(..)
  , ContainerStatus(..)
  , ExecResult(..)
    -- * Runtime Configuration (defined here to break circular dep)
  , RuntimeConfig(..)
  , Platform(..)
  , NetworkConfig(..)
  , defaultRuntimeConfig
  ) where

import Prelude

import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Effect (Effect)
import Effect.Aff (Aff)
import Forge.Aleph.Sandbox.Types (ContainerConfig)

-- ============================================================================
-- RUNTIME CONFIGURATION
-- ============================================================================

type RuntimeConfig =
  { runscPath :: String      -- Path to runsc binary
  , rootDir :: String        -- Container root directory
  , logDir :: String         -- Log directory
  , platform :: Platform     -- Execution platform
  , network :: NetworkConfig -- Network configuration
  }

data Platform
  = KVM            -- Hardware virtualization
  | PTRACE         -- ptrace-based (slower, more compatible)
  | SYSTRAP        -- syscall interception

derive instance eqPlatform :: Eq Platform
derive instance genericPlatform :: Generic Platform _

instance showPlatform :: Show Platform where
  show KVM = "KVM"
  show PTRACE = "PTRACE"
  show SYSTRAP = "SYSTRAP"

type NetworkConfig =
  { enableRawSockets :: Boolean
  , enableNetstack :: Boolean  -- gVisor's userspace network stack
  }

-- | Default runtime config
defaultRuntimeConfig :: RuntimeConfig
defaultRuntimeConfig =
  { runscPath: "/usr/local/bin/runsc"
  , rootDir: "/var/run/gvisor"
  , logDir: "/var/log/gvisor"
  , platform: SYSTRAP
  , network:
      { enableRawSockets: false
      , enableNetstack: true
      }
  }

-- ============================================================================
-- TYPES
-- ============================================================================

newtype ContainerId = ContainerId String

derive instance eqContainerId :: Eq ContainerId
derive newtype instance showContainerId :: Show ContainerId

data ContainerStatus
  = Created
  | Running
  | Stopped
  | Paused
  | Unknown String

derive instance eqContainerStatus :: Eq ContainerStatus
derive instance genericContainerStatus :: Generic ContainerStatus _

instance showContainerStatus :: Show ContainerStatus where
  show = genericShow

type ExecResult =
  { stdout :: String
  , stderr :: String
  , exitCode :: Int
  }

-- ============================================================================
-- CONTAINER LIFECYCLE
-- ============================================================================

-- | Create a new gVisor container from OCI bundle
-- |
-- | Creates the container but does not start it.
-- | Returns container ID on success.
foreign import createContainer :: RuntimeConfig -> ContainerConfig -> Aff (Either String ContainerId)

-- | Start a created container
foreign import startContainer :: RuntimeConfig -> ContainerId -> Aff (Either String Unit)

-- | Execute a command in a running container
foreign import execInContainer :: RuntimeConfig -> ContainerId -> Array String -> Aff (Either String ExecResult)

-- | Kill a running container (SIGKILL)
foreign import killContainer :: RuntimeConfig -> ContainerId -> Aff (Either String Unit)

-- | Delete a stopped container
foreign import deleteContainer :: RuntimeConfig -> ContainerId -> Aff (Either String Unit)

-- | Get current timestamp in milliseconds
foreign import getCurrentTimestamp :: Effect Number

-- ============================================================================
-- CONTAINER INFO
-- ============================================================================

-- | List all containers managed by runsc
foreign import listContainers :: RuntimeConfig -> Aff (Either String (Array ContainerId))

-- | Get status of a container
foreign import getContainerStatus :: RuntimeConfig -> ContainerId -> Aff (Either String ContainerStatus)

-- | Get container PID from runsc state
foreign import getContainerPid :: RuntimeConfig -> ContainerId -> Aff (Either String Int)
