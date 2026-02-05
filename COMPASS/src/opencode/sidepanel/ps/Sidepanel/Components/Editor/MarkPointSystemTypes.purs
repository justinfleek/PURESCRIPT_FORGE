{-|
Module      : Sidepanel.Components.Editor.MarkPointSystemTypes
Description : Types for mark & point system
Types for emacs-style mark & point system.
-}
module Sidepanel.Components.Editor.MarkPointSystemTypes where

import Prelude

-- | Mark & point state
type MarkPointState =
  { point :: Position  -- Current cursor position
  , mark :: Maybe Position  -- Current mark
  , markRing :: Array Position  -- Ring of recent marks (last 16)
  , globalMarkRing :: Array (String /\ Position)  -- Named global marks
  }

-- | Position in code
type Position =
  { file :: String
  , line :: Int
  , column :: Int
  }

-- | Mark
type Mark = Position

-- | Region (between mark and point)
type Region =
  { start :: Position
  , end :: Position
  , file :: String
  }
