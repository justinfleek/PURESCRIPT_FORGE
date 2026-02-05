-- | Keybinding utilities
module Opencode.Util.Keybind where

import Prelude
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Array as Array

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
parse str = 
  let parts = String.split (String.Pattern "+") str
      normalized = Array.map (String.trim >>> String.toUpper) parts
      hasModifier mod = Array.elem mod normalized
      key = Array.last normalized
  in case key of
    Nothing -> Nothing
    Just k -> Just
      { key: String.toUpper k
      , ctrl: hasModifier "CTRL" || hasModifier "CONTROL"
      , alt: hasModifier "ALT"
      , shift: hasModifier "SHIFT"
      , meta: hasModifier "META" || hasModifier "CMD"
      }

-- | Format a keybind to string
format :: Keybind -> String
format kb =
  let modifiers = Array.catMaybes
        [ if kb.ctrl then Just "Ctrl" else Nothing
        , if kb.alt then Just "Alt" else Nothing
        , if kb.shift then Just "Shift" else Nothing
        , if kb.meta then Just "Meta" else Nothing
        ]
      modStr = String.joinWith "+" modifiers
  in if Array.null modifiers
       then kb.key
       else modStr <> "+" <> kb.key

-- | Check if keybinds match
matches :: Keybind -> Keybind -> Boolean
matches a b = 
  a.key == b.key && 
  a.ctrl == b.ctrl && 
  a.alt == b.alt && 
  a.shift == b.shift && 
  a.meta == b.meta
