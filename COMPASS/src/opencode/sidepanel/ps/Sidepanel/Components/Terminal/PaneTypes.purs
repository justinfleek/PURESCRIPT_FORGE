{-|
Module      : Sidepanel.Components.Terminal.PaneTypes
Description : Types for terminal pane management (tmux-style splitting)
Types for managing terminal panes with splitting, resizing, and navigation.
-}
module Sidepanel.Components.Terminal.PaneTypes where

import Prelude

-- | Pane ID
type PaneId = String

-- | Split direction
data SplitDirection
  = Vertical  -- Split vertically (side by side)
  | Horizontal  -- Split horizontally (top/bottom)

derive instance eqSplitDirection :: Eq SplitDirection

-- | Pane layout structure
data PaneLayout
  = LeafPane PaneInfo  -- Terminal pane
  | SplitContainer SplitInfo PaneLayout PaneLayout  -- Container with two children

derive instance eqPaneLayout :: Eq PaneLayout

-- | Pane information
type PaneInfo =
  { id :: PaneId
  , terminalId :: String  -- Reference to terminal instance
  , size :: PaneSize  -- Current size
  , isActive :: Boolean  -- Is this pane active?
  , title :: String  -- Pane title
  }

-- | Split container information
type SplitInfo =
  { direction :: SplitDirection
  , splitRatio :: Number  -- 0.0 to 1.0, ratio of first child
  , isResizing :: Boolean  -- Currently being resized
  }

-- | Pane size
type PaneSize =
  { width :: Int  -- Width in columns
  , height :: Int  -- Height in rows
  }

-- | Pane state
type PaneState =
  { root :: PaneLayout
  , activePaneId :: Maybe PaneId
  , nextPaneId :: Int  -- Counter for generating IDs
  , panes :: PaneMap  -- Map of all panes
  }

-- | Map of pane IDs to pane info
type PaneMap = Array (PaneId /\ PaneInfo)

-- | Pane operation result
type PaneOperationResult =
  { success :: Boolean
  , newState :: PaneState
  , error :: Maybe String
  }

-- | Pane navigation direction
data NavigationDirection
  = Up
  | Down
  | Left
  | Right
  | Next
  | Previous

derive instance eqNavigationDirection :: Eq NavigationDirection
