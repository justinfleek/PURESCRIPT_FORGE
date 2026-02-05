{-|
Module      : Sidepanel.Components.Editor.RegisterSystemTypes
Description : Types for register system
Types for emacs-style register system (multiple named clipboards).
-}
module Sidepanel.Components.Editor.RegisterSystemTypes where

import Prelude

import Data.Map as Map

-- | Register ID (a-z, 0-9, or custom)
type RegisterId = String

-- | Register type
data RegisterType
  = TextRegister  -- Text content
  | PositionRegister  -- Cursor position
  | RectangleRegister  -- Rectangular region

derive instance eqRegisterType :: Eq RegisterType

-- | Register
type Register =
  { type_ :: RegisterType
  , content :: String  -- Text content (for text registers)
  , position :: Maybe Position  -- Position (for position registers)
  , rectangle :: Maybe Rectangle  -- Rectangle (for rectangle registers)
  }

-- | Position
type Position =
  { file :: String
  , line :: Int
  , column :: Int
  }

-- | Rectangle (rectangular selection)
type Rectangle =
  { start :: Position
  , end :: Position
  , lines :: Array String  -- Lines in rectangle
  }

-- | Register state
type RegisterState =
  { registers :: Map.Map RegisterId Register
  , lastUsed :: Maybe RegisterId
  }
