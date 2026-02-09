-- | TUI Thread management
-- | Ported from: opencode-dev/packages/forge/src/cli/cmd/tui/thread.ts
module Forge.CLI.Cmd.TUI.Thread where

import Prelude

import Data.Either (Either(..))
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

-- | Thread configuration
type ThreadConfig =
  { sessionId :: String
  , autoScroll :: Boolean
  }

-- | Start a TUI thread for a session
-- | Creates a rendering loop for the session's message stream
startThread :: ThreadConfig -> Aff (Either String Unit)
startThread config = fromEffectFnAff (startThreadFFI config)

-- | Stop the current TUI thread
stopThread :: Aff (Either String Unit)
stopThread = fromEffectFnAff stopThreadFFI

-- | FFI: Start thread
foreign import startThreadFFI :: ThreadConfig -> EffectFnAff (Either String Unit)

-- | FFI: Stop thread
foreign import stopThreadFFI :: EffectFnAff (Either String Unit)
