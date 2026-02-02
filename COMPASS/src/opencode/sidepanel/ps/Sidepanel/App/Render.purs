-- | App Render Functions
-- |
-- | Rendering functions for the root application component.
-- |
-- | Coeffect Equation:
-- |   Render : State -> H.ComponentHTML Action Slots m
-- |   with routing: currentRoute -> Panel -> View
-- |
-- | Module Coverage: Main render, panel rendering, toolbar
module Sidepanel.App.Render
  ( render
  , renderCurrentPanel
  , renderUndoRedoToolbar
  ) where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Data.Maybe (Maybe(..))
import Sidepanel.Router (Route(..))
import Sidepanel.State.AppState (AppState)
import Sidepanel.State.Settings (defaultSettings)
import Sidepanel.State.UndoRedo as UndoRedo
import Sidepanel.State.Actions (Action(..)) as StateActions
import Sidepanel.App.Types
  ( State
  , Action(..)
  , Slots
  , _sidebar
  , _dashboard
  , _session
  , _proof
  , _timeline
  , _settings
  , _alertSystem
  , _commandPalette
  , _terminalEmbed
  , _fileContextView
  , _diffViewer
  , _helpOverlay
  )
import Sidepanel.App.Helpers (getSessionForRoute)
import Sidepanel.Components.Sidebar as Sidebar
import Sidepanel.Components.Dashboard as Dashboard
import Sidepanel.Components.Session.SessionPanel as SessionPanel
import Sidepanel.Components.Proof.ProofPanel as ProofPanel
import Sidepanel.Components.Timeline.TimelineView as TimelineView
import Sidepanel.Components.Settings.SettingsPanel as SettingsPanel
import Sidepanel.Components.AlertSystem as AlertSystem
import Sidepanel.Components.KeyboardNavigation as KeyboardNavigation
import Sidepanel.Components.CommandPalette as CommandPalette
import Sidepanel.Components.TerminalEmbed as TerminalEmbed
import Sidepanel.Components.FileContextView as FileContextView
import Sidepanel.Components.DiffViewer as DiffViewer
import Sidepanel.Components.HelpOverlay as HelpOverlay

--------------------------------------------------------------------------------
-- | Main Render
--------------------------------------------------------------------------------

-- | Main render function
render :: forall m. State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ HP.class_ (H.ClassName "app") ]
    [ -- Alert system (always visible)
      HH.slot _alertSystem unit AlertSystem.component unit HandleAlertSystemOutput
    , -- Keyboard navigation (invisible, handles global shortcuts)
      HH.slot (H.Slot :: H.Slot KeyboardNavigation.Query KeyboardNavigation.Output Unit) unit KeyboardNavigation.component unit HandleKeyboardNavigationOutput
    , -- Command palette (overlay)
      HH.slot _commandPalette unit CommandPalette.component { wsClient: state.wsClient } HandleCommandPaletteOutput
    , -- Undo/Redo toolbar
      renderUndoRedoToolbar state
    , -- Sidebar
      HH.slot _sidebar unit Sidebar.component state.currentRoute HandleSidebarOutput
    , -- Main content
      HH.main
        [ HP.class_ (H.ClassName "app__main") ]
        [ renderCurrentPanel state ]
    , -- Help overlay
      HH.slot _helpOverlay unit HelpOverlay.component { visible: state.helpOverlayVisible } HandleHelpOverlayOutput
    ]

--------------------------------------------------------------------------------
-- | Undo/Redo Toolbar
--------------------------------------------------------------------------------

-- | Render undo/redo toolbar buttons
renderUndoRedoToolbar :: forall m. State -> H.ComponentHTML Action Slots m
renderUndoRedoToolbar state =
  let
    undoRedoState = state.appState.undoRedo
    canUndo = UndoRedo.canUndo undoRedoState
    canRedo = UndoRedo.canRedo undoRedoState
  in
    HH.div
      [ HP.class_ (H.ClassName "undo-redo-toolbar") ]
      [ HH.button
          [ HP.class_ (H.ClassName "btn-icon")
          , HP.disabled (not canUndo)
          , HP.title "Undo Ctrl+Z"
          , HE.onClick \_ -> HandleAppAction StateActions.Undo
          ]
          [ HH.text "<-" ]
      , HH.button
          [ HP.class_ (H.ClassName "btn-icon")
          , HP.disabled (not canRedo)
          , HP.title "Redo Ctrl+Shift+Z"
          , HE.onClick \_ -> HandleAppAction StateActions.Redo
          ]
          [ HH.text "->" ]
      ]

--------------------------------------------------------------------------------
-- | Panel Rendering
--------------------------------------------------------------------------------

-- | Render current panel based on route
renderCurrentPanel :: forall m. State -> H.ComponentHTML Action Slots m
renderCurrentPanel state = case state.currentRoute of
  Dashboard ->
    HH.slot _dashboard unit Dashboard.component
      { state: state.appState }
      (const HandleAppAction)
  
  Session sessionId ->
    HH.slot _session unit SessionPanel.component
      (getSessionForRoute state.appState sessionId)
      HandleSessionPanelOutput
  
  Proof ->
    HH.slot _proof unit ProofPanel.component
      { proofState: state.appState.proof, wsClient: state.wsClient }
      (const HandleAppAction)
  
  Timeline ->
    HH.slot _timeline unit TimelineView.component
      { snapshots: state.appState.snapshots
      , currentState: state.appState
      , wsClient: state.wsClient
      }
      HandleTimelineOutput
  
  Settings ->
    HH.slot _settings unit SettingsPanel.component
      { settings: defaultSettings, wsClient: state.wsClient }
      HandleSettingsOutput
  
  NotFound ->
    HH.div
      [ HP.class_ (H.ClassName "not-found") ]
      [ HH.h1_ [ HH.text "404" ]
      , HH.p_ [ HH.text "Page not found" ]
      ]
  
  Terminal ->
    HH.slot _terminalEmbed unit TerminalEmbed.component { wsClient: state.wsClient } HandleTerminalEmbedOutput
  
  FileContext ->
    HH.slot _fileContextView unit FileContextView.component { wsClient: state.wsClient } HandleFileContextViewOutput
  
  DiffViewer ->
    HH.slot _diffViewer unit DiffViewer.component { wsClient: state.wsClient } HandleDiffViewerOutput
