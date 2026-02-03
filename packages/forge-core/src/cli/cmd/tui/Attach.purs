-- | TUI Attach functionality
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/tui/attach.ts
module Forge.CLI.Cmd.TUI.Attach where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

type AttachConfig =
  { serverUrl :: String
  , sessionId :: String
  }

-- | Attach to a running forge server
attach :: AttachConfig -> Aff (Either String Unit)
attach config = notImplemented "CLI.Cmd.TUI.Attach.attach"
