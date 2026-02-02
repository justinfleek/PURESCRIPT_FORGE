-- | Debug Agent command
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/debug/agent.ts
module Opencode.CLI.Cmd.Debug.Agent where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Execute debug agent command
execute :: Aff (Either String Unit)
execute = notImplemented "CLI.Cmd.Debug.Agent.execute"
