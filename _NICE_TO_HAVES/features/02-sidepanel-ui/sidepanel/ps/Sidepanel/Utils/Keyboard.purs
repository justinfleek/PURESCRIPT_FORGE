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
import Data.Tuple (Tuple(..))
import Data.Array as Array
import Sidepanel.Router (Route(..))

-- | Keyboard shortcut mapping
type Shortcut = String

-- | Route shortcuts (Vim-style)
routeShortcuts :: Array (Shortcut /\ Route)
routeShortcuts =
  [ "1" /\ Dashboard
  , "2" /\ Session Nothing
  , "3" /\ Proof
  , "4" /\ Timeline
  , "5" /\ Settings
  , "g d" /\ Dashboard
  , "g s" /\ Session Nothing
  , "g p" /\ Proof
  , "g t" /\ Timeline
  , "/" /\ Dashboard  -- Search (placeholder)
  ]

-- | Find route for keyboard shortcut
findRouteForShortcut :: Shortcut -> Maybe Route
findRouteForShortcut shortcut =
  Array.findMap (\(s /\ r) -> if s == shortcut then Just r else Nothing) routeShortcuts

-- | Check if key combination matches shortcut
matchesShortcut :: String -> Shortcut -> Boolean
matchesShortcut keyCombo shortcut = keyCombo == shortcut

-- | Parse key event to shortcut string
parseKeyEvent :: String -> Maybe Shortcut
parseKeyEvent keyEvent =
  -- Placeholder - would parse actual keyboard events
  -- Format: "Ctrl+Shift+P" -> "ctrl+shift+p"
  Just keyEvent
