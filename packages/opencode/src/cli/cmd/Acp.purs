-- | ACP (Agent Collaboration Protocol) command
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/acp.ts
module Opencode.CLI.Cmd.Acp where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

type AcpArgs =
  { action :: String
  , target :: String
  }

-- | Execute the ACP command
execute :: AcpArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Acp.execute"
