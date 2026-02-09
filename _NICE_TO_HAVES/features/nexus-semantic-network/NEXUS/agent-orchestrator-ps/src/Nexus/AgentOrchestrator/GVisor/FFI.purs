module Nexus.AgentOrchestrator.GVisor.FFI where

import Prelude

import Effect.Aff (Aff)
import Data.Either (Either)
import Nexus.AgentOrchestrator.Types (SandboxConfig)

-- ============================================================================
-- TYPES
-- ============================================================================

newtype ContainerId = ContainerId String

derive instance eqContainerId :: Eq ContainerId
derive newtype instance showContainerId :: Show ContainerId

type ExecResult =
  { stdout :: String
  , stderr :: String
  , exitCode :: Int
  }

-- ============================================================================
-- CONTAINER LIFECYCLE
-- ============================================================================

-- | Create gVisor container from sandbox config
foreign import createGVisorContainer :: SandboxConfig -> String -> Aff (Either String ContainerId)

-- | Start a created container
foreign import startGVisorContainer :: ContainerId -> Aff (Either String Unit)

-- | Execute a command in a running container
foreign import execInGVisorContainer :: ContainerId -> Array String -> Aff (Either String ExecResult)

-- | Kill a running container
foreign import killGVisorContainer :: ContainerId -> Aff (Either String Unit)

-- | Delete a stopped container
foreign import deleteGVisorContainer :: ContainerId -> Aff (Either String Unit)
