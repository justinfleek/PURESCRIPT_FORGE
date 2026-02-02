-- | Keybinding utilities
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/util/keybind.ts
module Opencode.Util.Keybind where

import Prelude
import Data.Maybe (Maybe(..))

-- | Keybinding definition
type Keybind =
  { key :: String
  , ctrl :: Boolean
  , alt :: Boolean
  , shift :: Boolean
  , meta :: Boolean
  }

-- | Parse a keybind string like "Ctrl+Shift+A"
parse :: String -> Maybe Keybind
parse str = Nothing -- TODO: Implement

-- | Format a keybind to string
format :: Keybind -> String
format kb = "" -- TODO: Implement

-- | Check if keybinds match
matches :: Keybind -> Keybind -> Boolean
matches a b = 
  a.key == b.key && 
  a.ctrl == b.ctrl && 
  a.alt == b.alt && 
  a.shift == b.shift && 
  a.meta == b.meta
