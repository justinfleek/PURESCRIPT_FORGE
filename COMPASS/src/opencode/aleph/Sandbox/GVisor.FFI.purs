{-|
Module      : Aleph.Sandbox.GVisor.FFI
Description : Foreign function interface for gVisor runsc
= gVisor FFI

Foreign function interface for interacting with gVisor's runsc binary.
All functions are async and return Aff for proper error handling.
-}
module Aleph.Sandbox.GVisor.FFI
  ( -- * Container Lifecycle
    createContainer
  , startContainer
  , execInContainer
  , killContainer
  , deleteContainer
    -- * Container Info
  , listContainers
  , getContainerStatus
    -- * Utilities
  , getCurrentTimestamp
    -- * Types
  , ContainerId(..)
  , ContainerStatus(..)
  , ExecResult(..)
  ) where

import Prelude

import Data.Either (Either)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Effect.Aff (Aff)
import Aleph.Sandbox.Types (ContainerConfig)
import Aleph.Sandbox.GVisor (RuntimeConfig)

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
