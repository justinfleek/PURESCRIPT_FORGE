{-|
Module      : Sidepanel.Components.Editor.KeyboardMacrosTypes
Description : Types for keyboard macro system
Types for recording, storing, and replaying keyboard macros.
-}
module Sidepanel.Components.Editor.KeyboardMacrosTypes where

import Prelude

import Data.Maybe (Maybe)
import Data.Map as Map

-- | Macro ID
type MacroId = String

-- | Keyboard macro
type Macro =
  { id :: MacroId
  , name :: Maybe String
  , actions :: Array KeyboardAction
  , repeatCount :: Int
  }

-- | Keyboard action
type KeyboardAction =
  { type_ :: ActionType
  , key :: String
  , modifiers :: Modifiers
  , timestamp :: Number
  , target :: Maybe String
  }

-- | Action type
data ActionType
  = KeyPress
  | KeyRelease
  | TextInput
  | MouseClick
  | MouseMove
  | Command

derive instance eqActionType :: Eq ActionType

-- | Modifier keys
type Modifiers =
  { ctrl :: Boolean
  , shift :: Boolean
  , alt :: Boolean
  , meta :: Boolean
  }

-- | Macro state
type MacroState =
  { isRecording :: Boolean
  , currentMacro :: Maybe Macro
  , macros :: Map.Map MacroId Macro
  , lastMacroId :: Maybe MacroId
  , repeatCount :: Int
  }

-- | Macro operation
data MacroOperation
  = StartRecording
  | StopRecording
  | ExecuteMacro MacroId
  | ExecuteLastMacro
  | ExecuteWithRepeat MacroId Int
  | SaveMacro MacroId String
  | LoadMacro String
  | DeleteMacro MacroId
  | EditMacro MacroId (Array KeyboardAction)
  | ListMacros

derive instance eqMacroOperation :: Eq MacroOperation
