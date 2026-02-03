-- | ACP (Agent Collaboration Protocol) command
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/acp.ts
module Forge.CLI.Cmd.Acp where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

type AcpArgs =
  { action :: String
  , target :: String
  }

-- | Execute the ACP command
execute :: AcpArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Acp.execute"
