-- | Agent management command
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/agent.ts
module Opencode.CLI.Cmd.Agent where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

type AgentArgs =
  { list :: Boolean
  , info :: Maybe String
  }

-- | Execute the agent command
execute :: AgentArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Agent.execute"

-- | List available agents
listAgents :: Aff (Either String (Array String))
listAgents = notImplemented "CLI.Cmd.Agent.listAgents"
