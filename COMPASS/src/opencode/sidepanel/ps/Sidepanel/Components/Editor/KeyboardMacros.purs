{-|
Module      : Sidepanel.Components.Editor.KeyboardMacros
Description : Emacs-style keyboard macro recording and replay
Implements keyboard macro recording, editing, and replay functionality.
-}
module Sidepanel.Components.Editor.KeyboardMacros where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.Map as Map
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Class (liftEffect)
import Sidepanel.Components.Editor.KeyboardMacrosTypes
  ( Macro
  , MacroId
  , KeyboardAction
  , MacroState
  , MacroOperation(..)
  )

-- | Initial macro state
initialMacroState :: MacroState
initialMacroState =
  { isRecording: false
  , currentMacro: Nothing
  , macros: Map.empty
  , lastMacroId: Nothing
  , repeatCount: 1
  }

-- | Start recording macro
startRecording :: Ref MacroState -> Aff MacroId
startRecording stateRef = do
  state <- liftEffect $ Ref.read stateRef
  let newMacroId = generateMacroId state.lastMacroId
  let newMacro =
        { id: newMacroId
        , name: Nothing
        , actions: []
        , repeatCount: 1
        }
  
  liftEffect $ Ref.write state
    { isRecording = true
    , currentMacro = Just newMacro
    , lastMacroId = Just newMacroId
    } stateRef
  
  pure newMacroId

-- | Stop recording macro
stopRecording :: Ref MacroState -> Aff (Maybe Macro)
stopRecording stateRef = do
  state <- liftEffect $ Ref.read stateRef
  case state.currentMacro of
    Nothing -> pure Nothing
    Just macro -> do
      let updatedMacros = Map.insert macro.id macro state.macros
      liftEffect $ Ref.write state
        { isRecording = false
        , currentMacro = Nothing
        , macros = updatedMacros
        , lastMacroId = Just macro.id
        } stateRef
      pure (Just macro)

-- | Record action in macro
recordAction :: Ref MacroState -> KeyboardAction -> Aff Unit
recordAction stateRef action = do
  state <- liftEffect $ Ref.read stateRef
  case state.currentMacro of
    Nothing -> pure unit  -- Not recording
    Just macro -> do
      let updatedMacro = macro { actions = macro.actions <> [action] }
      liftEffect $ Ref.write state { currentMacro = Just updatedMacro } stateRef

-- | Execute macro
executeMacro :: Ref MacroState -> MacroId -> Aff Unit
executeMacro stateRef macroId = do
  state <- liftEffect $ Ref.read stateRef
  case Map.lookup macroId state.macros of
    Nothing -> pure unit  -- Macro not found
    Just macro -> do
      executeMacroActions macro.actions macro.repeatCount

-- | Execute last macro
executeLastMacro :: Ref MacroState -> Aff Unit
executeLastMacro stateRef = do
  state <- liftEffect $ Ref.read stateRef
  case state.lastMacroId of
    Nothing -> pure unit  -- No last macro
    Just macroId -> executeMacro stateRef macroId

-- | Execute macro with repeat count
executeMacroWithRepeat :: Ref MacroState -> MacroId -> Int -> Aff Unit
executeMacroWithRepeat stateRef macroId count = do
  state <- liftEffect $ Ref.read stateRef
  case Map.lookup macroId state.macros of
    Nothing -> pure unit
    Just macro -> do
      executeMacroActions macro.actions count

-- | Execute macro actions
executeMacroActions :: Array KeyboardAction -> Int -> Aff Unit
executeMacroActions actions count = do
  Array.for_ (Array.range 1 count) \_ -> do
    Array.for_ actions \action -> do
      executeAction action

-- | Execute single action
executeAction :: KeyboardAction -> Aff Unit
executeAction action = do
  -- Would dispatch to appropriate handler
  -- For now, placeholder
  pure unit

-- | Save macro with name
saveMacro :: Ref MacroState -> MacroId -> String -> Aff Unit
saveMacro stateRef macroId name = do
  state <- liftEffect $ Ref.read stateRef
  case Map.lookup macroId state.macros of
    Nothing -> pure unit  -- Macro not found
    Just macro -> do
      let updatedMacro = macro { name = Just name }
      let updatedMacros = Map.insert macroId updatedMacro state.macros
      liftEffect $ Ref.write state { macros = updatedMacros } stateRef

-- | Load macro by name
loadMacro :: Ref MacroState -> String -> Aff (Maybe Macro)
loadMacro stateRef name = do
  state <- liftEffect $ Ref.read stateRef
  let found = Array.find (\(_ /\ macro) -> macro.name == Just name) (Map.toUnfoldable state.macros)
  pure (map (\(_ /\ macro) -> macro) found)

-- | Delete macro
deleteMacro :: Ref MacroState -> MacroId -> Aff Unit
deleteMacro stateRef macroId = do
  state <- liftEffect $ Ref.read stateRef
  let updatedMacros = Map.delete macroId state.macros
  liftEffect $ Ref.write state { macros = updatedMacros } stateRef

-- | List all macros
listMacros :: Ref MacroState -> Aff (Array Macro)
listMacros stateRef = do
  state <- liftEffect $ Ref.read stateRef
  pure (Array.map (\(_ /\ macro) -> macro) (Map.toUnfoldable state.macros))

-- | Edit macro
editMacro :: Ref MacroState -> MacroId -> Array KeyboardAction -> Aff Unit
editMacro stateRef macroId newActions = do
  state <- liftEffect $ Ref.read stateRef
  case Map.lookup macroId state.macros of
    Nothing -> pure unit  -- Macro not found
    Just macro -> do
      let updatedMacro = macro { actions = newActions }
      let updatedMacros = Map.insert macroId updatedMacro state.macros
      liftEffect $ Ref.write state { macros = updatedMacros } stateRef

-- | Generate macro ID
generateMacroId :: Maybe MacroId -> MacroId
generateMacroId lastId = case lastId of
  Nothing -> "macro-1"
  Just id ->
    let parts = String.split (String.Pattern "-") id
        numPart = fromMaybe "0" (Array.last parts)
        num = case parseInt numPart of
          Nothing -> 0
          Just n -> n
    in
      "macro-" <> show (num + 1)

-- | Parse integer
parseInt :: String -> Maybe Int
parseInt str =
  let trimmed = String.trim str
      parsed = parseIntFFI trimmed
  in
    if parsed == 0 && trimmed /= "0" && String.length trimmed > 0 then
      Nothing
    else
      Just parsed

-- | FFI for integer parsing
foreign import parseIntFFI :: String -> Int
