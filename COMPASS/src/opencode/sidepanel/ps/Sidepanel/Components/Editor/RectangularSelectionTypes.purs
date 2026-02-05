{-|
Module      : Sidepanel.Components.Editor.RectangularSelectionTypes
Description : Types for rectangular selection
Types for rectangular (column-based) text selection.
-}
module Sidepanel.Components.Editor.RectangularSelectionTypes where

import Prelude

-- | Position
type Position =
  { line :: Int
  , column :: Int
  }

-- | Rectangle
type Rectangle =
  { start :: Position
  , end :: Position
  , lines :: Array String
  }

-- | Rectangular selection
type RectangularSelection =
  { start :: Position
  , end :: Position
  , rectangle :: Rectangle
  , isActive :: Boolean
  }

-- | Rectangle operation
data RectangleOperation
  = CopyRectangle  -- Copy rectangle to clipboard
  | KillRectangle  -- Delete rectangle
  | YankRectangle String  -- Insert rectangle
  | OpenRectangle  -- Insert spaces (open rectangle)
  | StringRectangle String  -- Replace with text

derive instance eqRectangleOperation :: Eq RectangleOperation
