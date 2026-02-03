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
import Sidepanel.State.AppState (AppState, initialState, Panel(..))
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

-- | App state
type State =
  { appState :: AppState
  , currentRoute :: Route
  , wsClient :: Maybe WS.WSClient
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
  { initialState: const { appState: initialState, currentRoute: Dashboard, wsClient: Nothing, helpOverlayVisible: false }
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
    , -- Main content
      HH.main
        [ HP.class_ (H.ClassName "app__main") ]
        [ renderCurrentPanel state ]
    , -- Help overlay
      HH.slot _helpOverlay unit HelpOverlay.component { visible: state.helpOverlayVisible } HandleHelpOverlayOutput
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
    Just
      { id: session.id
      , model: session.model
      , provider: "venice"  -- Would come from session data
      , startedAt: session.startedAt
      , promptTokens: session.promptTokens
      , completionTokens: session.completionTokens
      , cost: session.cost
      , messages: []  -- Would load from store
      }
  Nothing -> Nothing

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
      -- STUB: Clear all data
      -- TODO: Implement data clearing
      H.modify_ \s -> s { appState = initialState }

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
      KeyboardNavigation.NavigateToRoute route ->
        handleAction (HandleRouteChange route)
      KeyboardNavigation.Refresh ->
        -- Refresh current view (would reload data)
        pure unit
      KeyboardNavigation.ShowHelp ->
        -- STUB: Show keyboard shortcuts help
        -- TODO: Open help overlay
        pure unit
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
-- |             (for state reducer). Strips the `timestamp` field as it's not needed
-- |             in the reducer (reducer uses current time or preserves existing).
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
  }
