-- | TUI Thread management
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/tui/thread.ts
module Forge.CLI.Cmd.TUI.Thread where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

type ThreadConfig =
  { sessionId :: String
  , autoScroll :: Boolean
  }

-- | Start a TUI thread for a session
startThread :: ThreadConfig -> Aff (Either String Unit)
startThread config = notImplemented "CLI.Cmd.TUI.Thread.startThread"

-- | Stop the current TUI thread
stopThread :: Aff (Either String Unit)
stopThread = notImplemented "CLI.Cmd.TUI.Thread.stopThread"
