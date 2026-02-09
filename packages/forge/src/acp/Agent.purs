{-|
Module      : Forge.ACP.Agent
Description : Agent Control Protocol - Agent Management

ACP (Agent Control Protocol) provides a standardized interface for
managing AI agents. This module handles agent registration, discovery,
and capability negotiation.

== Coeffect Equation

@
  register   : ACPAgentConfig -> Graded (State * Network) Unit
  unregister : String -> Graded (State * Network) Unit
  list       : Unit -> Graded State (Array ACPAgentConfig)
@

== Agent Capabilities

Agents declare capabilities they support:
- `tools` - Can execute tools
- `streaming` - Supports streaming responses
- `vision` - Can process images
- `code` - Specialized for code tasks
-}
module Forge.ACP.Agent
  ( -- * Types
    ACPAgentConfig
  , AgentCapability(..)
  , AgentStatus(..)
  , RegisteredAgent
    -- * Registration
  , register
  , unregister
  , update
    -- * Discovery
  , list
  , get
  , getByCapability
    -- * Status
  , getStatus
  , setStatus
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Agent capability flags
data AgentCapability
  = CapTools          -- Can execute tools
  | CapStreaming      -- Supports streaming
  | CapVision         -- Can process images
  | CapCode           -- Code specialized
  | CapResearch       -- Research specialized
  | CapPlanning       -- Planning mode
  | CapCustom String  -- Custom capability

derive instance eqAgentCapability :: Eq AgentCapability

instance showAgentCapability :: Show AgentCapability where
  show CapTools = "tools"
  show CapStreaming = "streaming"
  show CapVision = "vision"
  show CapCode = "code"
  show CapResearch = "research"
  show CapPlanning = "planning"
  show (CapCustom s) = s

-- | Agent status
data AgentStatus
  = StatusIdle
  | StatusBusy
  | StatusError String
  | StatusOffline

derive instance eqAgentStatus :: Eq AgentStatus

instance showAgentStatus :: Show AgentStatus where
  show StatusIdle = "idle"
  show StatusBusy = "busy"
  show (StatusError e) = "error: " <> e
  show StatusOffline = "offline"

-- | ACP Agent configuration for registration
type ACPAgentConfig =
  { id :: String
  , name :: String
  , description :: String
  , capabilities :: Array String
  , version :: String
  , endpoint :: Maybe String  -- Optional remote endpoint
  }

-- | Registered agent with runtime state
type RegisteredAgent =
  { config :: ACPAgentConfig
  , status :: AgentStatus
  , registeredAt :: Number
  , lastActive :: Number
  }

-- ============================================================================
-- FFI
-- ============================================================================

-- | Store agent in registry
foreign import storeAgentFFI :: ACPAgentConfig -> Aff (Either String Unit)

-- | Remove agent from registry
foreign import removeAgentFFI :: String -> Aff (Either String Unit)

-- | Get all agents from registry
foreign import getAllAgentsFFI :: Aff (Array RegisteredAgent)

-- | Get agent by ID
foreign import getAgentFFI :: String -> Aff (Maybe RegisteredAgent)

-- | Update agent status
foreign import updateStatusFFI :: String -> String -> Aff (Either String Unit)

-- ============================================================================
-- REGISTRATION
-- ============================================================================

{-| Register an ACP agent.

Adds the agent to the registry and makes it available for use.
-}
register :: ACPAgentConfig -> Aff (Either String Unit)
register config = do
  -- Validate config
  case validateConfig config of
    Left err -> pure $ Left err
    Right _ -> storeAgentFFI config

{-| Unregister an ACP agent.

Removes the agent from the registry.
-}
unregister :: String -> Aff (Either String Unit)
unregister = removeAgentFFI

{-| Update an existing agent's configuration. -}
update :: ACPAgentConfig -> Aff (Either String Unit)
update config = do
  existing <- getAgentFFI config.id
  case existing of
    Nothing -> pure $ Left ("Agent not found: " <> config.id)
    Just _ -> storeAgentFFI config

-- ============================================================================
-- DISCOVERY
-- ============================================================================

{-| List all registered agents. -}
list :: Aff (Either String (Array ACPAgentConfig))
list = do
  agents <- getAllAgentsFFI
  pure $ Right $ map _.config agents

{-| Get a specific agent by ID. -}
get :: String -> Aff (Maybe ACPAgentConfig)
get agentId = do
  result <- getAgentFFI agentId
  pure $ map _.config result

{-| Get agents with a specific capability. -}
getByCapability :: String -> Aff (Array ACPAgentConfig)
getByCapability capability = do
  agents <- getAllAgentsFFI
  pure $ map _.config $ Array.filter (hasCapability capability) agents
  where
    hasCapability :: String -> RegisteredAgent -> Boolean
    hasCapability cap agent = Array.elem cap agent.config.capabilities

-- ============================================================================
-- STATUS
-- ============================================================================

{-| Get agent status. -}
getStatus :: String -> Aff (Maybe AgentStatus)
getStatus agentId = do
  result <- getAgentFFI agentId
  pure $ map _.status result

{-| Set agent status. -}
setStatus :: String -> AgentStatus -> Aff (Either String Unit)
setStatus agentId status = updateStatusFFI agentId (show status)

-- ============================================================================
-- VALIDATION
-- ============================================================================

validateConfig :: ACPAgentConfig -> Either String Unit
validateConfig config
  | config.id == "" = Left "Agent ID is required"
  | config.name == "" = Left "Agent name is required"
  | otherwise = Right unit
