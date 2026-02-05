{-|
Module      : Sidepanel.Components.Editor.KeyboardMacrosTypes
Description : Types for keyboard macro system
Types for recording, storing, and replaying keyboard macros.
-}
module Sidepanel.Components.Editor.KeyboardMacrosTypes where

import Prelude

import Data.Map as Map

-- | Macro ID
type MacroId = String

-- | Keyboard macro
type Macro =
  { id :: MacroId
  , name :: Maybe String  -- Optional name for saving
  , actions :: Array KeyboardAction  -- Recorded actions
  , repeatCount :: Int  -- Default repeat count
  }

-- | Keyboard action (simplified - would be more detailed)
type KeyboardAction =
  { type_ :: ActionType
  , key :: String  -- Key pressed
  , modifiers :: Modifiers  -- Modifier keys
  , timestamp :: Number  -- Timestamp (for timing-sensitive macros)
  , target :: Maybe String  -- Target element/component
  }

-- | Action type
data ActionType
  = KeyPress
  | KeyRelease
  | TextInput
  | MouseClick
  | MouseMove
  | Command  -- Editor command

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
  { isRecording :: Boolean  -- Currently recording?
  , currentMacro :: Maybe Macro  -- Macro being recorded
  , macros :: Map.Map MacroId Macro  -- Stored macros
  , lastMacroId :: Maybe MacroId  -- Last executed macro ID
  , repeatCount :: Int  -- Current repeat count
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
