-- | App Types
-- |
-- | Type definitions for the root application component.
-- |
-- | Coeffect Equation:
-- |   AppTypes : State * Action * Slots -> Component
-- |   with routing: Route -> Panel -> View
-- |
-- | Module Coverage: Slots, State, Action definitions
module Sidepanel.App.Types
  ( -- * Slots
    Slots
  , _sidebar
  , _dashboard
  , _session
  , _proof
  , _timeline
  , _settings
  , _balanceTracker
  , _tokenChart
  , _alertSystem
  , _keyboardNavigation
  , _commandPalette
  , _terminalEmbed
  , _fileContextView
  , _diffViewer
  , _helpOverlay
    -- * State
  , State
    -- * Actions
  , Action(..)
  ) where

import Prelude
import Halogen as H
import Data.Maybe (Maybe)
import Sidepanel.Router (Route)
import Sidepanel.State.AppState (AppState)
import Sidepanel.WebSocket.Client as WS
import Sidepanel.Api.Types (NotificationPayload, BalanceUpdatePayload)
import Sidepanel.Components.Sidebar as Sidebar
import Sidepanel.Components.Dashboard as Dashboard
import Sidepanel.Components.Session.SessionPanel as SessionPanel
import Sidepanel.Components.Proof.ProofPanel as ProofPanel
import Sidepanel.Components.Timeline.TimelineView as TimelineView
import Sidepanel.Components.Settings.SettingsPanel as SettingsPanel
import Sidepanel.Components.Balance.BalanceTracker as BalanceTracker
import Sidepanel.Components.TokenUsageChart as TokenUsageChart
import Sidepanel.Components.AlertSystem as AlertSystem
import Sidepanel.Components.KeyboardNavigation as KeyboardNavigation
import Sidepanel.Components.CommandPalette as CommandPalette
import Sidepanel.Components.TerminalEmbed as TerminalEmbed
import Sidepanel.Components.FileContextView as FileContextView
import Sidepanel.Components.DiffViewer as DiffViewer
import Sidepanel.Components.HelpOverlay as HelpOverlay
import Sidepanel.State.Actions as StateActions

--------------------------------------------------------------------------------
-- | Slots
--------------------------------------------------------------------------------

-- | Slots for child components
type Slots =
  ( sidebar :: H.Slot Sidebar.Query Sidebar.Output Unit
  , dashboard :: H.Slot Dashboard.Query Dashboard.Output Unit
  , session :: H.Slot SessionPanel.Query SessionPanel.Output Unit
  , proof :: H.Slot ProofPanel.Query Void Unit
  , timeline :: H.Slot TimelineView.Query TimelineView.Output Unit
  , settings :: H.Slot SettingsPanel.Query SettingsPanel.Output Unit
  , balanceTracker :: H.Slot BalanceTracker.Query BalanceTracker.Output Unit
  , tokenChart :: H.Slot TokenUsageChart.Query TokenUsageChart.Output Unit
  , alertSystem :: H.Slot AlertSystem.Query AlertSystem.Output Unit
  , keyboardNavigation :: H.Slot KeyboardNavigation.Query KeyboardNavigation.Output Unit
  , commandPalette :: H.Slot CommandPalette.Query CommandPalette.Output Unit
  , terminalEmbed :: H.Slot TerminalEmbed.Query TerminalEmbed.Output Unit
  , fileContextView :: H.Slot FileContextView.Query FileContextView.Output Unit
  , diffViewer :: H.Slot DiffViewer.Query DiffViewer.Output Unit
  , helpOverlay :: H.Slot HelpOverlay.Query HelpOverlay.Output Unit
  )

-- Slot proxies
_sidebar :: H.Slot Sidebar.Query Sidebar.Output Unit
_sidebar = H.Slot

_dashboard :: H.Slot Dashboard.Query Dashboard.Output Unit
_dashboard = H.Slot

_session :: H.Slot SessionPanel.Query SessionPanel.Output Unit
_session = H.Slot

_proof :: H.Slot ProofPanel.Query Void Unit
_proof = H.Slot

_timeline :: H.Slot TimelineView.Query TimelineView.Output Unit
_timeline = H.Slot

_settings :: H.Slot SettingsPanel.Query SettingsPanel.Output Unit
_settings = H.Slot

_balanceTracker :: H.Slot BalanceTracker.Query BalanceTracker.Output Unit
_balanceTracker = H.Slot

_tokenChart :: H.Slot TokenUsageChart.Query TokenUsageChart.Output Unit
_tokenChart = H.Slot

_alertSystem :: H.Slot AlertSystem.Query AlertSystem.Output Unit
_alertSystem = H.Slot

_keyboardNavigation :: H.Slot KeyboardNavigation.Query KeyboardNavigation.Output Unit
_keyboardNavigation = H.Slot

_commandPalette :: H.Slot CommandPalette.Query CommandPalette.Output Unit
_commandPalette = H.Slot

_terminalEmbed :: H.Slot TerminalEmbed.Query TerminalEmbed.Output Unit
_terminalEmbed = H.Slot

_fileContextView :: H.Slot FileContextView.Query FileContextView.Output Unit
_fileContextView = H.Slot

_diffViewer :: H.Slot DiffViewer.Query DiffViewer.Output Unit
_diffViewer = H.Slot

_helpOverlay :: H.Slot HelpOverlay.Query HelpOverlay.Output Unit
_helpOverlay = H.Slot

--------------------------------------------------------------------------------
-- | State
--------------------------------------------------------------------------------

-- | App state
type State =
  { appState :: AppState
  , currentRoute :: Route
  , wsClient :: Maybe WS.WSClient
  , helpOverlayVisible :: Boolean
  }

--------------------------------------------------------------------------------
-- | Actions
--------------------------------------------------------------------------------

-- | App actions
data Action
  = Initialize
  | HandleRouteChange Route
  | HandleSidebarOutput Sidebar.Output
  | HandleBalanceTrackerOutput BalanceTracker.Output
  | HandleSessionPanelOutput SessionPanel.Output
  | HandleTimelineOutput TimelineView.Output
  | HandleSettingsOutput SettingsPanel.Output
  | HandleTokenChartOutput TokenUsageChart.Output
  | HandleAlertSystemOutput AlertSystem.Output
  | HandleKeyboardNavigationOutput KeyboardNavigation.Output
  | HandleCommandPaletteOutput CommandPalette.Output
  | HandleTerminalEmbedOutput TerminalEmbed.Output
  | HandleFileContextViewOutput FileContextView.Output
  | HandleDiffViewerOutput DiffViewer.Output
  | HandleAppAction StateActions.Action
  | HandleBalanceUpdate BalanceUpdatePayload
  | PollWebSocketMessages
  | WebSocketConnected WS.WSClient
  | WebSocketDisconnected
  | OpenCommandPalette
  | CloseCommandPalette
  | OpenHelp
  | CloseHelp
  | HandleHelpOverlayOutput HelpOverlay.Output
  | HandleWebSocketNotification NotificationPayload
