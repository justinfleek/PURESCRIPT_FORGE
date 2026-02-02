-- | TUI Textarea Keybindings
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/tui/component/textarea-keybindings.ts
module Opencode.CLI.Cmd.TUI.Component.TextareaKeybindings where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Keybinding action
type KeyAction = String -> Effect Unit

-- | Default keybindings for textarea
type Keybindings =
  { submit :: String  -- Key to submit
  , cancel :: String  -- Key to cancel
  , newline :: String -- Key for newline
  , paste :: String   -- Key for paste
  }

-- | Get default keybindings
defaultKeybindings :: Keybindings
defaultKeybindings =
  { submit: "Enter"
  , cancel: "Escape"
  , newline: "Shift+Enter"
  , paste: "Ctrl+V"
  }

-- | Handle keypress in textarea
handleKeypress :: Keybindings -> String -> Effect (Maybe String)
handleKeypress bindings key = notImplemented "CLI.Cmd.TUI.Component.TextareaKeybindings.handleKeypress"
