{-|
Module      : Sidepanel.Components.Editor.MarkPointSystemTypes
Description : Types for mark & point system
Types for emacs-style mark & point system.
-}
module Sidepanel.Components.Editor.MarkPointSystemTypes where

import Prelude

import Data.Maybe (Maybe)
import Data.Tuple.Nested (type (/\))

-- | Mark & point state
type MarkPointState =
  { point :: Position
  , mark :: Maybe Position
  , markRing :: Array Position
  , globalMarkRing :: Array (String /\ Position)
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
