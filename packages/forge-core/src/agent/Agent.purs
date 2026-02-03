-- | Agent system
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/agent/agent.ts
module Forge.Agent.Agent where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | Agent mode
data AgentMode = Primary | Subagent

-- | Agent definition
type Agent =
  { id :: String
  , name :: String
  , description :: String
  , mode :: AgentMode
  , systemPrompt :: String
  }

-- | Get an agent by name
get :: String -> Aff (Maybe Agent)
get name = notImplemented "Agent.Agent.get"

-- | List all agents
list :: Aff (Either String (Array Agent))
list = notImplemented "Agent.Agent.list"

-- | Get default agent
getDefault :: Aff (Maybe Agent)
getDefault = notImplemented "Agent.Agent.getDefault"
