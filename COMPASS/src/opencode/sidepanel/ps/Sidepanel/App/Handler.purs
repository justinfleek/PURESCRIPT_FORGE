-- | App Action Handler
-- |
-- | Action handling logic for the root application component.
-- |
-- | Coeffect Equation:
-- |   Handler : Action -> H.HalogenM State Action Slots Void m Unit
-- |   with effects: State -o (State' * IO)
-- |
-- | Module Coverage: Initialize, routing, component outputs, WebSocket
module Sidepanel.App.Handler
  ( handleAction
  ) where

import Prelude
import Halogen as H
import Effect.Aff (Milliseconds(..), delay, forever)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array as Array
import Routing.Duplex (parse)
import Routing.Hash (matchesWith)
import Sidepanel.Router (Route(..), routeCodec, routeToPanel)
import Sidepanel.State.AppState (initialState)
import Sidepanel.State.Reducer (reduce)
import Sidepanel.State.Actions (Action(..)) as StateActions
import Sidepanel.WebSocket.Client as WS
import Sidepanel.Api.Types (ServerMessage(..))
import Sidepanel.Theme.CSS as ThemeCSS
import Sidepanel.Theme.Prism (generateHolographicTheme, fleekColors, MonitorType(..))
import Sidepanel.Theme.ModernTheme as ModernTheme
import Sidepanel.App.Types
  ( State
  , Action(..)
  , Slots
  , _alertSystem
  , _commandPalette
  )
import Sidepanel.App.Helpers
  ( routeNameToRoute
  , convertSettingsToAppState
  , convertBalanceUpdatePayload
  )
import Sidepanel.Components.Sidebar as Sidebar
import Sidepanel.Components.Balance.BalanceTracker as BalanceTracker
import Sidepanel.Components.Session.SessionPanel as SessionPanel
import Sidepanel.Components.Timeline.TimelineView as TimelineView
import Sidepanel.Components.Settings.SettingsPanel as SettingsPanel
import Sidepanel.Components.TokenUsageChart as TokenUsageChart
import Sidepanel.Components.AlertSystem as AlertSystem
import Sidepanel.Components.KeyboardNavigation as KeyboardNavigation
import Sidepanel.Components.CommandPalette as CommandPalette
import Sidepanel.Components.TerminalEmbed as TerminalEmbed
import Sidepanel.Components.FileContextView as FileContextView
import Sidepanel.Components.DiffViewer as DiffViewer
import Sidepanel.Components.HelpOverlay as HelpOverlay

--------------------------------------------------------------------------------
-- | Action Handler
--------------------------------------------------------------------------------

-- | Handle component actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Void m Unit
handleAction = case _ of
  Initialize -> do
    -- Apply modern theme (matching image styling)
    liftEffect $ ModernTheme.applyTheme ModernTheme.defaultThemeConfig
    
    -- Apply PRISM theme CSS (for compatibility)
    let base16Colors = generateHolographicTheme OLED
    let css = ThemeCSS.generateCSS base16Colors fleekColors
    liftEffect $ ThemeCSS.applyTheme css
    
    -- Initialize routing
    liftEffect $ matchesWith (parse routeCodec) \_ newRoute ->
      H.liftEffect $ pure unit
    
    -- Initialize WebSocket connection
    wsClient <- liftEffect $ WS.createClient WS.defaultConfig
    result <- WS.connect wsClient
    case result of
      Right _ -> do
        H.modify_ _ { wsClient = Just wsClient }
        void $ liftEffect $ WS.subscribe wsClient \_ -> pure unit
        void $ H.fork $ forever do
          delay (Milliseconds 100.0)
          handleAction PollWebSocketMessages
        pure unit
      Left _ -> pure unit

  HandleWebSocketNotification payload -> do
    void $ H.query _alertSystem unit $ H.tell $ AlertSystem.ShowNotificationQuery payload unit

  HandleBalanceUpdate payload -> do
    let balanceUpdate = convertBalanceUpdatePayload payload
    H.modify_ \s -> s { appState = reduce s.appState (StateActions.BalanceUpdated balanceUpdate) }

  PollWebSocketMessages -> do
    state <- H.get
    case state.wsClient of
      Just wsClient -> do
        msgs <- liftEffect $ WS.dequeueMessages wsClient
        Array.for_ msgs \msg -> case msg of
          BalanceUpdate payload ->
            handleAction (HandleBalanceUpdate payload)
          Notification payload ->
            handleAction (HandleWebSocketNotification payload)
          _ -> pure unit
      Nothing -> pure unit

  HandleRouteChange route -> do
    H.modify_ _ { currentRoute = route }
    H.modify_ \s -> s { appState = reduce s.appState (StateActions.SetActivePanel (routeToPanel route)) }

  HandleSidebarOutput (Sidebar.RouteSelected route) ->
    handleAction (HandleRouteChange route)

  HandleBalanceTrackerOutput output -> case output of
    BalanceTracker.AlertTriggered level ->
      H.modify_ \s -> s { appState = reduce s.appState (StateActions.AlertLevelChanged level) }
    BalanceTracker.SettingsRequested ->
      handleAction (HandleRouteChange Settings)
    BalanceTracker.RefreshRequested ->
      pure unit
    BalanceTracker.ProviderSelected pid ->
      pure unit

  HandleSessionPanelOutput output -> case output of
    SessionPanel.SessionCleared ->
      H.modify_ \s -> s { appState = reduce s.appState StateActions.SessionCleared }
    SessionPanel.SessionExported path ->
      pure unit

  HandleTimelineOutput output -> case output of
    TimelineView.SnapshotRestored id ->
      H.modify_ \s -> s { appState = reduce s.appState (StateActions.SnapshotRestored id) }
    TimelineView.SnapshotCreated id ->
      pure unit

  HandleSettingsOutput output -> case output of
    SettingsPanel.SettingsChanged newSettings ->
      let appSettings = convertSettingsToAppState newSettings
      in H.modify_ \s -> s { appState = s.appState { settings = appSettings } }
    SettingsPanel.DataCleared ->
      H.modify_ \s -> s { appState = initialState }

  HandleTokenChartOutput output -> case output of
    TokenUsageChart.ChartReady -> pure unit
    TokenUsageChart.ChartError err -> pure unit

  HandleAlertSystemOutput output -> case output of
    AlertSystem.AlertShown alert -> pure unit
    AlertSystem.AlertDismissed id -> pure unit

  HandleKeyboardNavigationOutput output -> case output of
    KeyboardNavigation.KeyboardActionTriggered action -> case action of
      KeyboardNavigation.Undo ->
        H.modify_ \s -> s { appState = reduce s.appState StateActions.Undo }
      KeyboardNavigation.Redo ->
        H.modify_ \s -> s { appState = reduce s.appState StateActions.Redo }
      KeyboardNavigation.OpenCommandPalette ->
        handleAction OpenCommandPalette
      KeyboardNavigation.NavigateToRoute route ->
        handleAction (HandleRouteChange route)
      KeyboardNavigation.Refresh ->
        pure unit
      KeyboardNavigation.ShowHelp ->
        pure unit
      KeyboardNavigation.Cancel ->
        handleAction CloseCommandPalette
      KeyboardNavigation.Confirm ->
        pure unit
      _ ->
        pure unit

  HandleCommandPaletteOutput output -> case output of
    CommandPalette.CommandExecuted id ->
      handleAction CloseCommandPalette
    CommandPalette.NavigateToRoute routeName ->
      let route = routeNameToRoute routeName
      in handleAction (HandleRouteChange route)
    CommandPalette.PaletteClosed ->
      handleAction CloseCommandPalette

  HandleTerminalEmbedOutput output -> case output of
    TerminalEmbed.TerminalReady -> pure unit
    TerminalEmbed.CommandExecuted cmd -> pure unit
    TerminalEmbed.TerminalError err -> pure unit

  HandleFileContextViewOutput output -> case output of
    FileContextView.FilesRemoved paths -> pure unit
    FileContextView.FilesAdded paths -> pure unit
    FileContextView.ContextRefreshed -> pure unit

  HandleDiffViewerOutput output -> case output of
    DiffViewer.HunkAccepted file hunkId -> pure unit
    DiffViewer.HunkRejected file hunkId -> pure unit
    DiffViewer.AllAcceptedInFile file -> pure unit
    DiffViewer.AllRejectedInFile file -> pure unit
    DiffViewer.AllAccepted -> pure unit
    DiffViewer.AllRejected -> pure unit
    DiffViewer.FilePreviewed file -> pure unit

  OpenCommandPalette -> do
    void $ H.query _commandPalette unit $ H.tell CommandPalette.Open

  CloseCommandPalette -> do
    void $ H.query _commandPalette unit $ H.tell CommandPalette.Close

  OpenHelp -> do
    H.modify_ _ { helpOverlayVisible = true }

  CloseHelp -> do
    H.modify_ _ { helpOverlayVisible = false }

  HandleHelpOverlayOutput HelpOverlay.OverlayClosed ->
    handleAction CloseHelp

  HandleAppAction action ->
    H.modify_ \s -> s { appState = reduce s.appState action }

  WebSocketConnected client ->
    H.modify_ _ { wsClient = Just client }

  WebSocketDisconnected ->
    H.modify_ _ { wsClient = Nothing }
