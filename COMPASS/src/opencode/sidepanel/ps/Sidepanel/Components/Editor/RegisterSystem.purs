{-|
Module      : Sidepanel.Components.Editor.RegisterSystem
Description : Emacs-style register system (multiple named clipboards)
Implements register system for storing text, positions, and rectangles in named slots.
-}
module Sidepanel.Components.Editor.RegisterSystem where

import Prelude

import Data.Map as Map
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Class (liftEffect)
import Sidepanel.Components.Editor.RegisterSystemTypes
  ( Register
  , RegisterId
  , RegisterType(..)
  , RegisterState
  , Position
  , Rectangle
  )

-- | Initial register state
initialRegisterState :: RegisterState
initialRegisterState =
  { registers: Map.empty
  , lastUsed: Nothing
  }

-- | Save text to register
saveTextToRegister :: Ref RegisterState -> RegisterId -> String -> Aff Unit
saveTextToRegister stateRef regId text = do
  state <- liftEffect $ Ref.read stateRef
  let register = { type_: TextRegister, content: text, position: Nothing, rectangle: Nothing }
  let updatedRegisters = Map.insert regId register state.registers
  liftEffect $ Ref.write state
    { registers = updatedRegisters
    , lastUsed = Just regId
    } stateRef

-- | Save position to register
savePositionToRegister :: Ref RegisterState -> RegisterId -> Position -> Aff Unit
savePositionToRegister stateRef regId position = do
  state <- liftEffect $ Ref.read stateRef
  let register = { type_: PositionRegister, content: "", position: Just position, rectangle: Nothing }
  let updatedRegisters = Map.insert regId register state.registers
  liftEffect $ Ref.write state
    { registers = updatedRegisters
    , lastUsed = Just regId
    } stateRef

-- | Save rectangle to register
saveRectangleToRegister :: Ref RegisterState -> RegisterId -> Rectangle -> Aff Unit
saveRectangleToRegister stateRef regId rectangle = do
  state <- liftEffect $ Ref.read stateRef
  let register = { type_: RectangleRegister, content: "", position: Nothing, rectangle: Just rectangle }
  let updatedRegisters = Map.insert regId register state.registers
  liftEffect $ Ref.write state
    { registers = updatedRegisters
    , lastUsed = Just regId
    } stateRef

-- | Get register
getRegister :: Ref RegisterState -> RegisterId -> Aff (Maybe Register)
getRegister stateRef regId = do
  state <- liftEffect $ Ref.read stateRef
  pure (Map.lookup regId state.registers)

-- | Insert register content
insertRegister :: Ref RegisterState -> RegisterId -> Aff (Maybe String)
insertRegister stateRef regId = do
  registerM <- getRegister stateRef regId
  case registerM of
    Nothing -> pure Nothing
    Just register -> do
      case register.type_ of
        TextRegister -> pure (Just register.content)
        PositionRegister -> pure Nothing  -- Would jump to position
        RectangleRegister -> pure Nothing  -- Would insert rectangle

-- | Jump to register position
jumpToRegister :: Ref RegisterState -> RegisterId -> Aff (Maybe Position)
jumpToRegister stateRef regId = do
  registerM <- getRegister stateRef regId
  case registerM of
    Nothing -> pure Nothing
    Just register -> pure register.position

-- | Insert rectangle from register
insertRectangle :: Ref RegisterState -> RegisterId -> Aff (Maybe Rectangle)
insertRectangle stateRef regId = do
  registerM <- getRegister stateRef regId
  case registerM of
    Nothing -> pure Nothing
    Just register -> pure register.rectangle

-- | List all registers
listRegisters :: Ref RegisterState -> Aff (Array (RegisterId /\ Register))
listRegisters stateRef = do
  state <- liftEffect $ Ref.read stateRef
  pure (Map.toUnfoldable state.registers)

-- | Delete register
deleteRegister :: Ref RegisterState -> RegisterId -> Aff Unit
deleteRegister stateRef regId = do
  state <- liftEffect $ Ref.read stateRef
  let updatedRegisters = Map.delete regId state.registers
  liftEffect $ Ref.write state { registers = updatedRegisters } stateRef

-- | Clear all registers
clearRegisters :: Ref RegisterState -> Aff Unit
clearRegisters stateRef = do
  liftEffect $ Ref.write initialRegisterState stateRef
