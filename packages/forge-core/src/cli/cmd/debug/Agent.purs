-- | Debug Agent command
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/debug/agent.ts
module Forge.CLI.Cmd.Debug.Agent where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Execute debug agent command
execute :: Aff (Either String Unit)
execute = notImplemented "CLI.Cmd.Debug.Agent.execute"
