-- | TUI Textarea Keybindings
module Forge.CLI.Cmd.TUI.Component.TextareaKeybindings where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe(..))
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
-- | Returns Just action if the key matches a binding, Nothing otherwise
handleKeypress :: Keybindings -> String -> Effect (Maybe String)
handleKeypress bindings key = pure $
  if key == bindings.submit then Just "submit"
  else if key == bindings.cancel then Just "cancel"
  else if key == bindings.newline then Just "newline"
  else if key == bindings.paste then Just "paste"
  else Nothing
