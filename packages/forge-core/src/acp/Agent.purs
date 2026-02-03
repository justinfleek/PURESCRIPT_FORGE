-- | ACP Agent
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/acp/agent.ts
module Forge.ACP.Agent where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | ACP Agent configuration
type ACPAgentConfig =
  { id :: String
  , name :: String
  , capabilities :: Array String
  }

-- | Register an ACP agent
register :: ACPAgentConfig -> Aff (Either String Unit)
register config = notImplemented "ACP.Agent.register"

-- | Unregister an ACP agent
unregister :: String -> Aff (Either String Unit)
unregister agentId = notImplemented "ACP.Agent.unregister"

-- | List registered agents
list :: Aff (Either String (Array ACPAgentConfig))
list = notImplemented "ACP.Agent.list"
