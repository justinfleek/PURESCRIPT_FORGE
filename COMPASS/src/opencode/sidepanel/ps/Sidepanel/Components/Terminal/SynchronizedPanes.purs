{-|
Module      : Sidepanel.Components.Terminal.SynchronizedPanes
Description : Synchronized panes - send commands to all panes simultaneously
Implements tmux-style synchronized panes functionality.
-}
module Sidepanel.Components.Terminal.SynchronizedPanes where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Class (liftEffect)
import Sidepanel.Components.Terminal.PaneTypes (PaneId, PaneState)

-- | Synchronized panes state
type SynchronizedPanesState =
  { isEnabled :: Boolean
  , synchronizedPanes :: Array PaneId  -- Panes that are synchronized
  }

-- | Initial synchronized panes state
initialSynchronizedPanesState :: SynchronizedPanesState
initialSynchronizedPanesState =
  { isEnabled: false
  , synchronizedPanes: []
  }

-- | Enable synchronized panes
enableSynchronizedPanes :: Ref SynchronizedPanesState -> Array PaneId -> Aff Unit
enableSynchronizedPanes stateRef paneIds = do
  liftEffect $ Ref.write
    { isEnabled: true
    , synchronizedPanes: paneIds
    } stateRef

-- | Disable synchronized panes
disableSynchronizedPanes :: Ref SynchronizedPanesState -> Aff Unit
disableSynchronizedPanes stateRef = do
  liftEffect $ Ref.modify_ (\s -> s { isEnabled = false }) stateRef

-- | Toggle synchronized panes
toggleSynchronizedPanes :: Ref SynchronizedPanesState -> Array PaneId -> Aff Unit
toggleSynchronizedPanes stateRef paneIds = do
  state <- liftEffect $ Ref.read stateRef
  if state.isEnabled then
    disableSynchronizedPanes stateRef
  else
    enableSynchronizedPanes stateRef paneIds

-- | Send command to all synchronized panes
sendToSynchronizedPanes :: Ref SynchronizedPanesState -> String -> Aff Unit
sendToSynchronizedPanes stateRef command = do
  state <- liftEffect $ Ref.read stateRef
  if state.isEnabled then
    Array.for_ state.synchronizedPanes \paneId -> do
      sendCommandToPane paneId command
  else
    pure unit

-- | Send command to a specific pane
sendCommandToPane :: PaneId -> String -> Aff Unit
sendCommandToPane paneId command = do
  -- Would send command to terminal instance
  -- For now, placeholder
  pure unit

-- | Check if panes are synchronized
isSynchronized :: Ref SynchronizedPanesState -> Aff Boolean
isSynchronized stateRef = do
  state <- liftEffect $ Ref.read stateRef
  pure state.isEnabled

-- | Get synchronized panes
getSynchronizedPanes :: Ref SynchronizedPanesState -> Aff (Array PaneId)
getSynchronizedPanes stateRef = do
  state <- liftEffect $ Ref.read stateRef
  pure state.synchronizedPanes

-- | Add pane to synchronization group
addPaneToSync :: Ref SynchronizedPanesState -> PaneId -> Aff Unit
addPaneToSync stateRef paneId = do
  liftEffect $ Ref.modify_ (\s ->
    if Array.elem paneId s.synchronizedPanes then
      s
    else
      s { synchronizedPanes = s.synchronizedPanes <> [paneId] }
  ) stateRef

-- | Remove pane from synchronization group
removePaneFromSync :: Ref SynchronizedPanesState -> PaneId -> Aff Unit
removePaneFromSync stateRef paneId = do
  liftEffect $ Ref.modify_ (\s ->
    s { synchronizedPanes = Array.filter (\id -> id /= paneId) s.synchronizedPanes }
  ) stateRef
