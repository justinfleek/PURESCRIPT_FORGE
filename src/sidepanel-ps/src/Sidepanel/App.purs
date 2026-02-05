-- | Main App Component - Root Application Component with Routing and State Management
-- |
-- | **What:** The root Halogen component that orchestrates the entire sidepanel application,
-- |         including routing, WebSocket connection, theme management, and all child components
-- |         (sidebar, dashboard, session panel, proof panel, timeline, settings, etc.).
-- | **Why:** Provides the top-level application structure, manages global state transitions,
-- |         handles routing between panels, and coordinates communication between components
-- |         via WebSocket and local state updates.
-- | **How:** Uses Halogen component architecture with:
-- |         - Hash-based routing (Routing.Duplex) for panel navigation
-- |         - WebSocket client for real-time communication with Bridge Server
-- |         - State reducer pattern for predictable state updates
-- |         - Component slots for all child components
-- |         - Theme system (PRISM) for styling
-- |
-- | **Dependencies:**
-- | - `Sidepanel.State.Reducer`: Pure state reducer for state transitions
-- | - `Sidepanel.Router`: Route definitions and parsing
-- | - `Sidepanel.WebSocket.Client`: WebSocket communication
-- | - `Sidepanel.Theme.Prism`: Theme generation and application
-- | - All child components (Sidebar, Dashboard, SessionPanel, etc.)
-- |
-- | **Mathematical Foundation:**
-- | - **State Invariant:** `appState` is always valid and synchronized with `currentRoute`.
-- |   When route changes, `appState.ui.activePanel` is updated to match.
-- | - **Component Tree Invariant:** All child components are always rendered (some may be
-- |   hidden via CSS). This ensures consistent component lifecycle.
-- | - **WebSocket Invariant:** `wsClient` is `Nothing` when disconnected, `Just client`
-- |   when connected. State updates are synchronized via WebSocket messages.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.App as App
-- |
-- | -- In main entry point:
-- | main = do
-- |   HA.runHalogenAff do
-- |     body <- HA.awaitBody
-- |     runUI App.component unit body
-- |
-- | -- Component handles all initialization, routing, and state management internally
-- | ```
-- |
-- | Based on spec 50-DASHBOARD-LAYOUT.md
module Sidepanel.App where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect, liftEffect)
import Data.Maybe (Maybe(..))
import Effect.Aff (Milliseconds(..), delay, forever, forkAff)
import Data.Array as Array
import Routing.Duplex (parse)
import Routing.Hash (matchesWith)
import Sidepanel.Router (Route(..), routeCodec, routeToPanel, parseRoute)
import Sidepanel.State.AppState (AppState, initialState, Panel(..), Message(..), MessageRole(..), MessageUsage(..), ToolCall(..), ToolStatus(..))
import Sidepanel.Components.Session.SessionPanel as SessionPanel
import Sidepanel.State.Reducer (reduce)
import Sidepanel.State.Actions (Action(..), BalanceUpdate)
import Sidepanel.Components.Sidebar as Sidebar
import Sidepanel.Components.Dashboard as Dashboard
import Sidepanel.Components.Session.SessionPanel as SessionPanel
import Sidepanel.Components.Proof.ProofPanel as ProofPanel
import Sidepanel.Components.Timeline.TimelineView as TimelineView
import Sidepanel.Components.Settings.SettingsPanel as SettingsPanel
import Sidepanel.Components.Balance.BalanceTracker as BalanceTracker
import Sidepanel.Components.TokenUsageChart as TokenUsageChart
import Sidepanel.Components.AlertSystem as AlertSystem
import Sidepanel.Api.Types (NotificationPayload)
import Sidepanel.Components.CommandPalette as CommandPalette
import Sidepanel.Components.TerminalEmbed as TerminalEmbed
import Sidepanel.Components.FileContextView as FileContextView
import Sidepanel.Components.DiffViewer as DiffViewer
import Sidepanel.Components.KeyboardNavigation as KeyboardNavigation
import Sidepanel.Components.HelpOverlay as HelpOverlay
import Sidepanel.Components.Session.SessionTabs as SessionTabs
import Sidepanel.Components.Session.BranchDialog as BranchDialog
import Sidepanel.Components.Search.SearchView as SearchView
import Sidepanel.Components.QuickActions.QuickActions as QuickActions
import Sidepanel.Components.Performance.PerformanceProfiler as PerformanceProfiler
import Sidepanel.WebSocket.Client as WS
import Sidepanel.State.Settings (defaultSettings, Settings as FullSettings)
import Sidepanel.Api.Types (ServerMessage(..), NotificationPayload, BalanceUpdatePayload)
import Sidepanel.Theme.CSS as ThemeCSS
import Sidepanel.Theme.Prism (generateHolographicTheme, fleekColors, OLED)
import Sidepanel.State.UndoRedo as UndoRedo
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Effect.Aff (Milliseconds(..), delay, forever, forkAff)
import Effect.Aff.Class (class MonadAff)
import Data.Array as Array

-- | Slots for child components - Component slot type definitions
-- |
-- | **Purpose:** Defines all child component slots used in the App component.
-- | **Slots:**
-- | - `sidebar`: Navigation sidebar component
-- | - `dashboard`: Main dashboard view
-- | - `session`: Session detail panel
-- | - `proof`: Lean4 proof panel
-- | - `timeline`: State timeline/snapshots view
-- | - `settings`: Settings panel
-- | - `balanceTracker`: Balance tracking widget
-- | - `tokenChart`: Token usage chart
-- | - `alertSystem`: Alert notification system
-- | - `keyboardNavigation`: Global keyboard shortcuts handler
-- | - `commandPalette`: Command palette overlay
-- | - `terminalEmbed`: Embedded terminal
-- | - `fileContextView`: File context viewer
-- | - `diffViewer`: Diff viewer component
-- | - `helpOverlay`: Help overlay component
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

_sidebar = H.Slot :: H.Slot Sidebar.Query Sidebar.Output Unit
_dashboard = H.Slot :: H.Slot Dashboard.Query Dashboard.Output Unit
_session = H.Slot :: H.Slot SessionPanel.Query SessionPanel.Output Unit
_proof = H.Slot :: H.Slot ProofPanel.Query Void Unit
_timeline = H.Slot :: H.Slot TimelineView.Query TimelineView.Output Unit
_settings = H.Slot :: H.Slot SettingsPanel.Query SettingsPanel.Output Unit
_balanceTracker = H.Slot :: H.Slot BalanceTracker.Query BalanceTracker.Output Unit
_tokenChart = H.Slot :: H.Slot TokenUsageChart.Query TokenUsageChart.Output Unit
_alertSystem = H.Slot :: H.Slot AlertSystem.Query AlertSystem.Output Unit
_keyboardNavigation = H.Slot :: H.Slot KeyboardNavigation.Query KeyboardNavigation.Output Unit
_commandPalette = H.Slot :: H.Slot CommandPalette.Query CommandPalette.Output Unit
_terminalEmbed = H.Slot :: H.Slot TerminalEmbed.Query TerminalEmbed.Output Unit
_fileContextView = H.Slot :: H.Slot FileContextView.Query FileContextView.Output Unit
_diffViewer = H.Slot :: H.Slot DiffViewer.Query DiffViewer.Output Unit
_helpOverlay = H.Slot :: H.Slot HelpOverlay.Query HelpOverlay.Output Unit
_sessionTabs = H.Slot :: H.Slot SessionTabs.Query SessionTabs.Output Unit
_branchDialog = H.Slot :: H.Slot BranchDialog.Query BranchDialog.Output Unit
_searchView = H.Slot :: H.Slot SearchView.Query SearchView.Output Unit
_quickActions = H.Slot :: H.Slot QuickActions.Query QuickActions.Output Unit
_performanceProfiler = H.Slot :: H.Slot PerformanceProfiler.Query PerformanceProfiler.Output Unit

-- | App state
type State =
  { appState :: AppState
  , currentRoute :: Route
  , wsClient :: Maybe WS.WSClient
  , helpOverlayVisible :: Boolean
  }

-- | App actions - All possible actions the App component can handle
-- |
-- | **Purpose:** Defines all actions that can be dispatched to the App component,
-- |             including initialization, routing, component outputs, and WebSocket events.
-- | **Categories:**
-- | - Initialization: `Initialize`
-- | - Routing: `HandleRouteChange`, `OpenCommandPalette`, `CloseCommandPalette`
-- | - Component outputs: `HandleSidebarOutput`, `HandleSessionPanelOutput`, etc.
-- | - State updates: `HandleAppAction` (wraps Sidepanel.State.Actions.Action)
-- | - WebSocket: `WebSocketConnected`, `WebSocketDisconnected`, `HandleWebSocketNotification`
-- | - UI: `OpenHelp`, `CloseHelp`
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
  | HandleAppAction Action
  | WebSocketConnected WS.WSClient
  | WebSocketDisconnected
  | OpenCommandPalette
  | CloseCommandPalette
  | OpenHelp
  | CloseHelp
  | HandleHelpOverlayOutput HelpOverlay.Output
  | HandleWebSocketNotification NotificationPayload
  | HandleSearchViewOutput SearchView.Output
  | HandleQuickActionsOutput QuickActions.Output
  | HandlePerformanceProfilerOutput PerformanceProfiler.Output
  | OpenSearch
  | CloseSearch
  | OpenPerformanceProfiler
  | ClosePerformanceProfiler
  | OpenGameSelection

-- | App component - Root Halogen component factory
-- |
-- | **Purpose:** Creates the root application component that manages routing, state,
-- |             WebSocket connection, and all child components.
-- | **Returns:** Halogen component with no input (Unit) and no output (Void)
-- | **Side Effects:** Component initialization triggers WebSocket connection and theme application
-- |
-- | **Initialization:**
-- | - Applies PRISM theme CSS (Holographic theme with OLED monitor settings)
-- | - Initializes hash-based routing
-- | - Creates and connects WebSocket client
-- | - Subscribes to WebSocket notifications
-- |
-- | **Example:**
-- | ```purescript
-- | runUI App.component unit body
-- | ```
component :: forall q m. MonadAff m => H.Component q Unit Void m
component = H.mkComponent
  { initialState: const { appState: initialState, currentRoute: Dashboard, wsClient: Nothing, helpOverlayVisible: false, searchViewVisible: false, performanceProfilerVisible: false }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

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
      HH.slot _sidebar unit Sidebar.component state.currentRoute
        HandleSidebarOutput
    , -- Session tabs (if on session route)
      if shouldShowTabs state.currentRoute then
        HH.slot _sessionTabs unit SessionTabs.component state.appState.sessionTabs HandleSessionTabsOutput
      else
        HH.text ""
    , -- Main content
      HH.main
        [ HP.class_ (H.ClassName "app__main") ]
        [ renderCurrentPanel state ]
    , -- Help overlay
      HH.slot _helpOverlay unit HelpOverlay.component { visible: state.helpOverlayVisible } HandleHelpOverlayOutput
    , -- Search view (overlay)
      HH.slot _searchView unit SearchView.component
        { visible: state.searchViewVisible, wsClient: state.wsClient }
        HandleSearchViewOutput
    , -- Quick actions (on Dashboard)
      if state.currentRoute == Dashboard then
        HH.slot _quickActions unit QuickActions.component
          { appState: state.appState, wsClient: state.wsClient }
          HandleQuickActionsOutput
      else
        HH.text ""
    , -- Performance profiler (overlay)
      if state.performanceProfilerVisible then
        HH.slot _performanceProfiler unit PerformanceProfiler.component
          { sessionId: state.appState.activeSessionId, wsClient: state.wsClient }
          HandlePerformanceProfilerOutput
      else
        HH.text ""
    , -- Branch dialog
      HH.slot _branchDialog unit BranchDialog.component
        { sessionId: getBranchDialogSessionId state.appState
        , messageIndex: 0  -- Would come from message selection
        , visible: false  -- Would be controlled by state
        }
        HandleBranchDialogOutput
    ]

-- | Render undo/redo toolbar buttons - Undo/Redo UI controls
-- |
-- | **Purpose:** Renders undo and redo buttons in the toolbar, with disabled state
-- |             based on undo/redo availability.
-- | **Parameters:**
-- | - `state`: Current component state
-- | **Returns:** Halogen HTML for undo/redo toolbar
-- | **Side Effects:** None (pure rendering)
-- |
-- | **Button States:**
-- | - Undo button: Disabled if `canUndo` is false
-- | - Redo button: Disabled if `canRedo` is false
-- |
-- | **Keyboard Shortcuts:**
-- | - Undo: Ctrl+Z
-- | - Redo: Ctrl+Shift+Z
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
          , HE.onClick \_ -> HandleAppAction Undo
          ]
          [ HH.text "↶" ]
      , HH.button
          [ HP.class_ (H.ClassName "btn-icon")
          , HP.disabled (not canRedo)
          , HP.title "Redo Ctrl+Shift+Z"
          , HE.onClick \_ -> HandleAppAction Redo
          ]
          [ HH.text "↷" ]
      ]

-- | Render current panel - Route-based panel rendering
-- |
-- | **Purpose:** Renders the appropriate panel component based on the current route.
-- | **Parameters:**
-- | - `state`: Current component state
-- | **Returns:** Halogen HTML for the current panel
-- | **Side Effects:** None (pure rendering)
-- |
-- | **Panel Mapping:**
-- | - `Dashboard` -> Dashboard component
-- | - `Session sessionId` -> SessionPanel component
-- | - `Proof` -> ProofPanel component
-- | - `Timeline` -> TimelineView component
-- | - `Settings` -> SettingsPanel component
-- | - `Terminal` -> TerminalEmbed component
-- | - `FileContext` -> FileContextView component
-- | - `DiffViewer` -> DiffViewer component
-- | - `NotFound` -> 404 error page
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

-- | Get session for route - Extract session data for SessionPanel
-- |
-- | **Purpose:** Converts AppState session data to SessionPanel.Session format.
-- | **Parameters:**
-- | - `appState`: Current application state
-- | - `sessionId`: Optional session ID (currently unused, would filter by ID)
-- | **Returns:** Maybe SessionPanel.Session (Nothing if no active session)
-- | **Side Effects:** None (pure function)
-- |
-- | **Note:** Currently returns the active session if it exists. Future enhancement:
-- |          would filter by sessionId to support multiple sessions.
getSessionForRoute :: AppState -> Maybe String -> Maybe SessionPanel.Session
getSessionForRoute appState sessionId = case appState.session of
  Just session ->
    -- Convert AppState messages to SessionPanel messages
    let
      convertedMessages = Array.map convertMessage appState.messages
    in
      Just
        { id: session.id
        , model: session.model
        , provider: "venice"  -- Would come from session data
        , startedAt: session.startedAt
        , promptTokens: session.promptTokens
        , completionTokens: session.completionTokens
        , cost: session.cost
        , messages: convertedMessages
        }
  Nothing -> Nothing
  where
    -- Convert AppState.Message to SessionPanel.Message
    convertMessage :: AppState.Message -> SessionPanel.Message
    convertMessage msg =
      { id: msg.id
      , role: convertRole msg.role
      , content: msg.content
      , timestamp: msg.timestamp
      , usage: map convertUsage msg.usage
      , toolCalls: Array.map convertToolCall msg.toolCalls
      }
    
    convertRole :: AppState.MessageRole -> SessionPanel.Role
    convertRole = case _ of
      AppState.User -> SessionPanel.User
      AppState.Assistant -> SessionPanel.Assistant
      AppState.System -> SessionPanel.System
      AppState.Tool -> SessionPanel.Tool
    
    convertUsage :: AppState.MessageUsage -> SessionPanel.MessageUsage
    convertUsage usage =
      { promptTokens: usage.promptTokens
      , completionTokens: usage.completionTokens
      , cost: usage.cost
      }
    
    convertToolCall :: AppState.ToolCall -> SessionPanel.ToolCall
    convertToolCall tool =
      { name: tool.name
      , status: convertToolStatus tool.status
      , durationMs: tool.durationMs
      }
    
    convertToolStatus :: AppState.ToolStatus -> SessionPanel.ToolStatus
    convertToolStatus = case _ of
      AppState.Pending -> SessionPanel.Pending
      AppState.Running -> SessionPanel.Running
      AppState.Completed -> SessionPanel.Completed
      AppState.Failed -> SessionPanel.Failed

-- | Handle action - Main action handler for App component
-- |
-- | **Purpose:** Handles all actions dispatched to the App component, including
-- |             initialization, routing, component outputs, state updates, and WebSocket events.
-- | **Parameters:**
-- | - `action`: Action to handle
-- | **Returns:** HalogenM computation that updates state and/or triggers side effects
-- | **Side Effects:** Various (state updates, WebSocket operations, component queries)
-- |
-- | **Action Categories:**
-- | 1. **Initialization:** `Initialize` - Sets up theme, routing, WebSocket
-- | 2. **Routing:** `HandleRouteChange`, `OpenCommandPalette`, `CloseCommandPalette`
-- | 3. **Component Outputs:** `HandleSidebarOutput`, `HandleSessionPanelOutput`, etc.
-- | 4. **State Updates:** `HandleAppAction` - Wraps Sidepanel.State.Actions.Action
-- | 5. **WebSocket:** `WebSocketConnected`, `WebSocketDisconnected`, `HandleWebSocketNotification`
-- | 6. **UI:** `OpenHelp`, `CloseHelp`
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Void m Unit
handleAction = case _ of
  -- | Initialize - Component initialization action
  -- |
  -- | **Purpose:** Initializes the application on component mount:
  -- |             - Applies PRISM theme CSS (Holographic theme with OLED settings)
  -- |             - Sets up hash-based routing
  -- |             - Creates and connects WebSocket client
  -- |             - Subscribes to WebSocket notifications
  -- | **Side Effects:**
  -- |             - Applies CSS theme to document
  -- |             - Creates WebSocket connection
  -- |             - Registers routing listener
  Initialize -> do
    -- Apply PRISM theme CSS (using Holographic as default starting colors)
    let base16Colors = generateHolographicTheme OLED
    let css = ThemeCSS.generateCSS base16Colors fleekColors
    liftEffect $ ThemeCSS.applyTheme css
    
    -- Initialize routing
    liftEffect $ matchesWith (parse routeCodec) \_ newRoute ->
      H.liftEffect $ pure unit  -- Would trigger HandleRouteChange
    
    -- Initialize WebSocket connection
    wsClient <- liftEffect $ WS.createClient WS.defaultConfig
    result <- WS.connect wsClient
    case result of
      Right _ -> do
        H.modify_ _ { wsClient = Just wsClient }
        
        -- Subscribe to WebSocket notifications (messages are queued automatically)
        void $ liftEffect $ WS.subscribe wsClient \_ -> pure unit
        
        -- Start polling for queued messages
        void $ H.fork $ forever do
          delay (Milliseconds 100.0)  -- Poll every 100ms
          handleAction PollWebSocketMessages
        
        pure unit
      Left _ -> pure unit
  
  HandleWebSocketNotification payload -> do
    -- Forward notification to AlertSystem via query
    void $ H.query _alertSystem unit $ H.tell $ AlertSystem.ShowNotificationQuery payload unit

  HandleBalanceUpdate payload -> do
    -- Convert BalanceUpdatePayload to BalanceUpdate and dispatch
    let balanceUpdate = convertBalanceUpdatePayload payload
    H.modify_ \s -> s { appState = reduce s.appState (BalanceUpdated balanceUpdate) }

  PollWebSocketMessages -> do
    -- Poll WebSocket message queue and dispatch actions
    state <- H.get
    case state.wsClient of
      Just wsClient -> do
        msgs <- liftEffect $ WS.dequeueMessages wsClient
        Array.for_ msgs \msg -> case msg of
          BalanceUpdate payload ->
            handleAction (HandleBalanceUpdate payload)
          Notification payload ->
            handleAction (HandleWebSocketNotification payload)
          _ -> pure unit  -- Other message types handled elsewhere
      Nothing -> pure unit

  HandleRouteChange route -> do
    H.modify_ _ { currentRoute = route }
    -- Update app state panel
    H.modify_ \s -> s { appState = reduce s.appState (SetActivePanel (routeToPanel route)) }

  HandleSidebarOutput (Sidebar.RouteSelected route) ->
    handleAction (HandleRouteChange route)

  HandleBalanceTrackerOutput output -> case output of
    BalanceTracker.AlertTriggered level ->
      H.modify_ \s -> s { appState = reduce s.appState (AlertLevelChanged level) }
    BalanceTracker.SettingsRequested ->
      handleAction (HandleRouteChange Settings)
    BalanceTracker.RefreshRequested ->
      -- Would refresh balance via WebSocket
      pure unit
    BalanceTracker.ProviderSelected pid ->
      -- Would update display mode
      pure unit

  HandleSessionPanelOutput output -> case output of
    SessionPanel.SessionCleared ->
      H.modify_ \s -> s { appState = reduce s.appState SessionCleared }
    SessionPanel.SessionExported path ->
      -- Would show notification
      pure unit

  HandleTimelineOutput output -> case output of
    TimelineView.SnapshotRestored id ->
      H.modify_ \s -> s { appState = reduce s.appState (SnapshotRestored id) }
    TimelineView.SnapshotCreated id ->
      -- Would show notification
      pure unit

  HandleSettingsOutput output -> case output of
    SettingsPanel.SettingsChanged newSettings ->
      -- Convert from Sidepanel.State.Settings.Settings to AppState.Settings
      let appSettings = convertSettingsToAppState newSettings
      in H.modify_ \s -> s { appState = s.appState { settings = appSettings } }
    SettingsPanel.DataCleared ->
      -- Clear all data: reset to initial state and clear session history
      H.modify_ \s -> s { appState = initialState { sessionHistory = [] } }

  HandleTokenChartOutput output -> case output of
    TokenUsageChart.ChartReady ->
      pure unit
    TokenUsageChart.ChartError err ->
      -- Would show error alert
      pure unit

  HandleAlertSystemOutput output -> case output of
    AlertSystem.AlertShown alert ->
      -- Alert shown, could log or track
      pure unit
    AlertSystem.AlertDismissed id ->
      -- Alert dismissed
      pure unit

  HandleKeyboardNavigationOutput output -> case output of
    KeyboardNavigation.KeyboardActionTriggered action -> case action of
      KeyboardNavigation.Undo ->
        H.modify_ \s -> s { appState = reduce s.appState Undo }
      
      KeyboardNavigation.Redo ->
        H.modify_ \s -> s { appState = reduce s.appState Redo }
      
      KeyboardNavigation.OpenCommandPalette ->
        handleAction OpenCommandPalette
      KeyboardNavigation.OpenSearch ->
        handleAction OpenSearch
      KeyboardNavigation.NavigateToRoute route ->
        handleAction (HandleRouteChange route)
      KeyboardNavigation.Refresh ->
        -- Refresh current view (would reload data)
        pure unit
      KeyboardNavigation.ShowHelp ->
        handleAction OpenHelp
      KeyboardNavigation.Cancel ->
        handleAction CloseCommandPalette
      KeyboardNavigation.Confirm ->
        -- Confirm current action (context-dependent)
        pure unit
      _ ->
        -- Other navigation actions handled by components
        pure unit

  HandleCommandPaletteOutput output -> case output of
    CommandPalette.CommandExecuted id ->
      -- Command executed
      handleAction CloseCommandPalette
    CommandPalette.NavigateToRoute routeName ->
      -- Navigate to route based on command
      let route = routeNameToRoute routeName
      in handleAction (HandleRouteChange route)
    CommandPalette.PaletteClosed ->
      -- Command palette closed
      handleAction CloseCommandPalette

  HandleTerminalEmbedOutput output -> case output of
    TerminalEmbed.TerminalReady ->
      pure unit
    TerminalEmbed.CommandExecuted cmd ->
      -- Command executed in terminal
      pure unit
    TerminalEmbed.TerminalError err ->
      -- Terminal error occurred
      pure unit

  HandleFileContextViewOutput output -> case output of
    FileContextView.FilesRemoved paths ->
      -- Files removed from context
      pure unit
    FileContextView.FilesAdded paths ->
      -- Files added to context
      pure unit
    FileContextView.ContextRefreshed ->
      -- Context refreshed
      pure unit

  HandleDiffViewerOutput output -> case output of
    DiffViewer.HunkAccepted file hunkId ->
      -- Hunk accepted
      pure unit
    DiffViewer.HunkRejected file hunkId ->
      -- Hunk rejected
      pure unit
    DiffViewer.AllAcceptedInFile file ->
      -- All hunks in file accepted
      pure unit
    DiffViewer.AllRejectedInFile file ->
      -- All hunks in file rejected
      pure unit
    DiffViewer.AllAccepted ->
      -- All changes accepted
      pure unit
    DiffViewer.AllRejected ->
      -- All changes rejected
      pure unit
    DiffViewer.FilePreviewed file ->
      -- File preview requested
      pure unit

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
  
  HandleSessionTabsOutput output -> case output of
    SessionTabs.TabSelected sessionId -> do
      H.modify_ \s -> s { appState = reduce s.appState (SessionSwitched sessionId) }
      -- Navigate to session route
      handleAction (HandleRouteChange (Session (Just sessionId)))
    
    SessionTabs.TabClosed sessionId -> do
      H.modify_ \s -> s { appState = reduce s.appState (SessionClosed sessionId) }
      -- If closed session was active, navigate away
      state <- H.get
      if state.appState.activeSessionId == Just sessionId then
        handleAction (HandleRouteChange Dashboard)
      else
        pure unit
    
    SessionTabs.TabsReordered newOrder -> do
      H.modify_ \s -> s { appState = reduce s.appState (TabsReordered newOrder) }
    
    SessionTabs.NewTabRequested -> do
      -- Create new session (would generate ID, get model from settings, etc.)
      -- For now, just show a placeholder - would need Bridge API call
      pure unit
  
  HandleBranchDialogOutput output -> case output of
    BranchDialog.BranchCreated sessionId messageIndex description -> do
      -- Generate branch session ID (would use UUID generator)
      let branchSessionId = "branch-" <> sessionId <> "-" <> show messageIndex
      let branchTitle = if description == "" then "Branch" else description
      H.modify_ \s -> s { appState = reduce s.appState (SessionBranchCreated sessionId messageIndex description branchSessionId branchTitle) }
      -- Navigate to branch session
      handleAction (HandleRouteChange (Session (Just branchSessionId)))
    
    BranchDialog.BranchCancelled ->
      pure unit
  
  HandleSearchViewOutput output -> case output of
    SearchView.ResultSelected result -> do
      -- Navigate to result based on type
      case result.type_ of
        SearchView.SessionResult -> do
          case result.metadata.sessionId of
            Just sessionId -> handleAction (HandleRouteChange (Session (Just sessionId)))
            Nothing -> pure unit
        SearchView.MessageResult -> do
          -- Navigate to session and scroll to message
          case result.metadata.sessionId of
            Just sessionId -> handleAction (HandleRouteChange (Session (Just sessionId)))
            Nothing -> pure unit
        SearchView.FileResult -> do
          -- Would open file in editor (via Bridge API)
          pure unit
        SearchView.ProofResult -> do
          handleAction (HandleRouteChange Proof)
        SearchView.RecordingResult -> do
          -- Would open recording player
          pure unit
      handleAction CloseSearch
    
    SearchView.SearchClosed ->
      handleAction CloseSearch
  
  HandleQuickActionsOutput output -> case output of
    QuickActions.ActionTriggered action -> do
      -- Handle action based on ID
      case action.id of
        "session.new" -> do
          -- Create new session
          handleAction (HandleRouteChange (Session Nothing))
        "nav.search" -> do
          handleAction OpenSearch
        "export.session" -> do
          -- Export current session
          state <- H.get
          case state.appState.activeSessionId of
            Just sessionId -> do
              case state.wsClient of
                Just client -> do
                  result <- liftEffect $ Bridge.exportSession client
                    { sessionId: sessionId
                    , format: "markdown"
                    , includeTimeline: Just true
                    }
                  case result of
                    Right response -> pure unit  -- Would trigger download
                    Left _ -> pure unit
                Nothing -> pure unit
            Nothing -> pure unit
        "nav.timeline" -> do
          handleAction (HandleRouteChange Timeline)
        "nav.settings" -> do
          handleAction (HandleRouteChange Settings)
        "snapshot.create" -> do
          -- Create snapshot
          state <- H.get
          case state.wsClient of
            Just client -> do
              result <- liftEffect $ Bridge.saveSnapshot client
                { trigger: "manual"
                , description: Just "Quick action snapshot"
                }
              case result of
                Right response -> pure unit
                Left _ -> pure unit
            Nothing -> pure unit
        _ -> pure unit
  
  HandlePerformanceProfilerOutput output -> case output of
    PerformanceProfiler.SnapshotCreated id -> do
      -- Snapshot created, could show notification
      pure unit
  
  OpenSearch -> do
    H.modify_ _ { searchViewVisible = true }
  
  CloseSearch -> do
    H.modify_ _ { searchViewVisible = false }
  
  OpenPerformanceProfiler -> do
    H.modify_ _ { performanceProfilerVisible = true }
  
  ClosePerformanceProfiler -> do
    H.modify_ _ { performanceProfilerVisible = false }

  WebSocketConnected client ->
    H.modify_ _ { wsClient = Just client }

  WebSocketDisconnected ->
    H.modify_ _ { wsClient = Nothing }

-- | Convert route name string to Route - Parse route string to Route type
-- |
-- | **Purpose:** Converts a route name string (from command palette or other sources)
-- |             to a Route type for navigation.
-- | **Parameters:**
-- | - `name`: Route name string (e.g., "dashboard", "timeline", "settings")
-- | **Returns:** Route type (defaults to Dashboard if name is unknown)
-- | **Side Effects:** None (pure function)
-- |
-- | **Supported Routes:**
-- | - "dashboard" -> Dashboard
-- | - "timeline" -> Timeline
-- | - "file-context" -> FileContext
-- | - "terminal" -> Terminal
-- | - "settings" -> Settings
-- | - "proof" -> Proof
-- | - "diff" -> DiffViewer
-- | - Unknown -> Dashboard (default)
routeNameToRoute :: String -> Route
routeNameToRoute name = case name of
  "dashboard" -> Dashboard
  "timeline" -> Timeline
  "file-context" -> FileContext
  "terminal" -> Terminal
  "settings" -> Settings
  "proof" -> Proof
  "diff" -> DiffViewer
  _ -> Dashboard

-- | Convert FullSettings to AppSettings - Settings type conversion
-- |
-- | **Purpose:** Converts from `Sidepanel.State.Settings.Settings` (full settings type)
-- |             to `AppSettings` (simplified subset used in AppState). Preserves what
-- |             can be mapped, uses defaults for fields not present in FullSettings.
-- | **Parameters:**
-- | - `fullSettings`: Complete settings from SettingsPanel
-- | **Returns:** AppSettings for AppState
-- | **Side Effects:** None (pure function)
-- |
-- | **Mapping:**
-- | - Theme -> MonitorType (Dark -> OLED, Light -> LCD, System -> OLED)
-- | - Other fields (veniceApiKey, forgeApiUrl, leanLspUrl) use defaults or Nothing
-- |   (would need to be stored separately or added to FullSettings)
convertSettingsToAppState :: FullSettings -> AppSettings
convertSettingsToAppState fullSettings =
  { veniceApiKey: Nothing  -- Not in FullSettings, would need to be stored separately
  , forgeApiUrl: "http://localhost:4096"  -- Not in FullSettings, use default
  , leanLspUrl: Nothing  -- Not in FullSettings, would need to be stored separately
  , monitorType: case fullSettings.appearance.theme of
      Sidepanel.State.Settings.Dark -> OLED
      Sidepanel.State.Settings.Light -> LCD
      Sidepanel.State.Settings.System -> OLED  -- Default to OLED for system
  , blackBalance: 0.11  -- Not in FullSettings, use default
  }

-- | Convert BalanceUpdatePayload to BalanceUpdate - WebSocket payload conversion
-- |
-- | **Purpose:** Converts a `BalanceUpdatePayload` (from WebSocket) to a `BalanceUpdate`
-- |             (for state reducer). Includes timestamp for history tracking.
-- | **Parameters:**
-- | - `payload`: Balance update payload from WebSocket
-- | **Returns:** BalanceUpdate for reducer
-- | **Side Effects:** None (pure function)
convertBalanceUpdatePayload :: BalanceUpdatePayload -> BalanceUpdate
convertBalanceUpdatePayload payload =
  { diem: payload.diem
  , flk: payload.flk
  , usd: payload.usd
  , effective: payload.effective
  , consumptionRate: payload.consumptionRate
  , timeToDepletion: payload.timeToDepletion
  , todayUsed: payload.todayUsed
  , timestamp: payload.timestamp  -- Include timestamp for history tracking
  }

-- | Should show tabs - Determine if session tabs should be displayed
-- |
-- | **Purpose:** Returns true if session tabs should be shown for the current route.
-- | **Parameters:**
-- | - `route`: Current route
-- | **Returns:** Boolean indicating if tabs should be shown
shouldShowTabs :: Route -> Boolean
shouldShowTabs = case _ of
  Session _ -> true
  _ -> false

-- | Get branch dialog session ID - Get session ID for branch dialog
-- |
-- | **Purpose:** Returns the session ID to use for the branch dialog (active session).
-- | **Parameters:**
-- | - `appState`: Current application state
-- | **Returns:** Session ID string (empty string if no active session)
getBranchDialogSessionId :: AppState -> String
getBranchDialogSessionId appState = case appState.activeSessionId of
  Just id -> id
  Nothing -> ""
