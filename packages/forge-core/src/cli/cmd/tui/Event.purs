-- | TUI Event handling
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/tui/event.ts
module Forge.CLI.Cmd.TUI.Event where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | TUI Event types
data TUIEvent
  = KeyPress String
  | Resize Int Int
  | Focus Boolean
  | Paste String
  | Mouse MouseEvent

type MouseEvent =
  { x :: Int
  , y :: Int
  , button :: Int
  }

-- | Event handler type
type EventHandler = TUIEvent -> Effect Unit

-- | Subscribe to TUI events
subscribe :: EventHandler -> Effect Unit
subscribe handler = notImplemented "CLI.Cmd.TUI.Event.subscribe"

-- | Unsubscribe from TUI events
unsubscribe :: Effect Unit
unsubscribe = notImplemented "CLI.Cmd.TUI.Event.unsubscribe"
