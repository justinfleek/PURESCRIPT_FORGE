{-|
Module      : Sidepanel.Components.Terminal.CopyModeTypes
Description : Types for copy mode
Types for terminal copy mode (tmux-style scrollback navigation).
-}
module Sidepanel.Components.Terminal.CopyModeTypes where

import Prelude

-- | Copy mode state
type CopyModeState =
  { lines :: Array String  -- Scrollback lines
  , currentLine :: Int  -- Current line in scrollback
  , currentColumn :: Int  -- Current column in line
  , selectionStart :: Maybe Position  -- Selection start position
  , selectionEnd :: Maybe Position  -- Selection end position
  , searchQuery :: String  -- Current search query
  , searchResults :: Array Position  -- Search result positions
  , currentSearchIndex :: Int  -- Current search result index
  , isActive :: Boolean  -- Is copy mode active?
  }

-- | Position in scrollback
type Position =
  { line :: Int
  , column :: Int
  }

-- | Selection
type Selection =
  { start :: Position
  , end :: Position
  , text :: String
  }

-- | Search direction
data SearchDirection
  = Forward
  | Backward

derive instance eqSearchDirection :: Eq SearchDirection

-- | Copy mode action
data CopyModeAction
  = MoveUp
  | MoveDown
  | MoveLeft
  | MoveRight
  | MoveToStartOfLine
  | MoveToEndOfLine
  | MoveToTop
  | MoveToBottom
  | PageUp
  | PageDown
  | StartSelection
  | EndSelection
  | CopySelection
  | SearchForward String
  | SearchBackward String
  | NextSearchResult
  | PreviousSearchResult
  | Exit

derive instance eqCopyModeAction :: Eq CopyModeAction
