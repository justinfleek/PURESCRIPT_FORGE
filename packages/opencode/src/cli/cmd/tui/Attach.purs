-- | TUI Attach functionality
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/tui/attach.ts
module Opencode.CLI.Cmd.TUI.Attach where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

type AttachConfig =
  { serverUrl :: String
  , sessionId :: String
  }

-- | Attach to a running opencode server
attach :: AttachConfig -> Aff (Either String Unit)
attach config = notImplemented "CLI.Cmd.TUI.Attach.attach"
