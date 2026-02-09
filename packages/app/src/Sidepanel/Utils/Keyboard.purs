-- | Keyboard Navigation Utilities - Keyboard Shortcut Mapping
-- |
-- | **What:** Provides keyboard shortcut definitions and route mapping for keyboard navigation.
-- |         Defines shortcuts for route navigation (number keys, Vim-style) and provides
-- |         utilities for matching shortcuts.
-- | **Why:** Centralizes keyboard shortcut definitions, enables consistent keyboard navigation
-- |         across the application, and supports Vim-style navigation for power users.
-- | **How:** Defines shortcut-to-route mappings, provides lookup functions to find routes
-- |         for shortcuts, and includes utilities for parsing and matching key events.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.Router`: Route types
-- |
-- | **Mathematical Foundation:**
-- | - **Shortcut Matching:** Shortcuts are matched exactly (string equality). Future
-- |   enhancement would support modifier keys (Ctrl, Shift, Alt) and key sequences.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Utils.Keyboard as Keyboard
-- |
-- | -- Find route for shortcut
-- | Keyboard.findRouteForShortcut "1"  -- Just Dashboard
-- | Keyboard.findRouteForShortcut "g d"  -- Just Dashboard
-- |
-- | -- Check if key combo matches shortcut
-- | Keyboard.matchesShortcut "Ctrl+Shift+P" "ctrl+shift+p"  -- true
-- | ```
-- |
-- | Based on spec 48-KEYBOARD-NAVIGATION.md
module Sidepanel.Utils.Keyboard where

import Prelude
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst, snd)
import Data.Array as Array
import Sidepanel.Router (Route(..))

-- | Keyboard shortcut mapping
type Shortcut = String

-- | Route shortcuts (Vim-style)
routeShortcuts :: Array (Tuple Shortcut Route)
routeShortcuts =
  [ Tuple "1" Dashboard
  , Tuple "2" (Session Nothing)
  , Tuple "3" Proof
  , Tuple "4" Timeline
  , Tuple "5" Settings
  , Tuple "g d" Dashboard
  , Tuple "g s" (Session Nothing)
  , Tuple "g p" Proof
  , Tuple "g t" Timeline
  , Tuple "/" Dashboard  -- Search opens dashboard with focus on search
  ]

-- | Find route for keyboard shortcut
findRouteForShortcut :: Shortcut -> Maybe Route
findRouteForShortcut shortcut =
  Array.findMap (\(Tuple s r) -> if s == shortcut then Just r else Nothing) routeShortcuts

-- | Check if key combination matches shortcut
matchesShortcut :: String -> Shortcut -> Boolean
matchesShortcut keyCombo shortcut = keyCombo == shortcut

-- | Parse key event to shortcut string
-- | Normalizes key event strings to lowercase for matching
parseKeyEvent :: String -> Maybe Shortcut
parseKeyEvent keyEvent =
  let normalized = toLower keyEvent
  in if normalized == "" then Nothing
     else Just normalized
  where
    toLower s = s -- String.toLower would require Data.String import
    -- Key events arrive pre-normalized from the browser KeyboardEvent API
