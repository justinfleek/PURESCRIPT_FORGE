-- | Dashboard Component - Main Application Dashboard View
-- |
-- | **What:** Displays the main dashboard view showing balance, session, and proof
-- |         status widgets. This is the default landing view when the sidepanel opens.
-- | **Why:** Provides users with a unified view of their current system state, token
-- |         usage, active sessions, and Lean4 proof status. Centralizes key information
-- |         in a single view.
-- | **How:** Integrates with AppState to display three key widgets:
-- |         - Balance widget: Shows Venice Diem balance and token consumption
-- |         - Session widget: Shows current active session details
-- |         - Proof widget: Shows Lean4 LSP connection and goal status
-- |
-- | **Dependencies:**
-- | - `Sidepanel.State.AppState`: Provides application state
-- | - `Sidepanel.State.Balance`: Provides BalanceState type
-- |
-- | **Mathematical Foundation:**
-- | - **State Invariant:** Component's State is always equal to the AppState passed as
-- |   Input. This ensures the dashboard always reflects the current application state.
-- | - **Rendering Invariant:** All three widgets (balance, session, proof) are always
-- |   rendered, even if their data is empty (showing "No data" messages).
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.Dashboard as Dashboard
-- |
-- | -- In parent component:
-- | HH.slot _dashboard unit Dashboard.component
-- |   { state: appState }
-- |   (const HandleAppAction)
-- |
-- | -- To update dashboard state:
-- | H.query _dashboard unit $ H.tell $ Dashboard.UpdateState newAppState
-- | ```
-- |
-- | Based on spec 50-DASHBOARD-LAYOUT.md
module Sidepanel.Components.Dashboard where

import Prelude
import Data.Array as Array
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Aff (Milliseconds(..), delay, forever, forkAff, killFiber, error, Fiber)
import Type.Proxy (Proxy(..))
import Sidepanel.State.AppState (AppState, SessionState, ProofState)
import Sidepanel.State.Balance (BalanceState, FlkBalance)
import Sidepanel.Utils.Currency (formatDiem, formatFLK, formatUSD)
import Sidepanel.Utils.Time (TimeRemaining, getTimeUntilReset)
import Sidepanel.Components.Balance.DiemTracker as DiemTracker
import Sidepanel.Components.TokenUsageChart as TokenChart
import Sidepanel.Components.CostBreakdownChart as CostChart
import Sidepanel.Components.CostBreakdownChart (CostBreakdown)
import Sidepanel.Components.Session.SessionSummary as SessionSummary
import Sidepanel.Utils.TokenUsage as TokenUsage
import Effect.Class (liftEffect)
import Sidepanel.FFI.DateTime (getCurrentDateTime)

-- | Component input - Dashboard component input props
-- |
-- | **Purpose:** Receives the current application state to display in the dashboard.
-- | **Fields:**
-- | - `state`: Current application state
type Input = 
  { state :: AppState
  }

-- | Component output - Dashboard component output events
-- |
-- | **Purpose:** Currently unused - dashboard is a display-only component.
-- | **Future:** May emit events for widget interactions.
data Output = NoOp

-- TimeRange is now imported from TokenUsage module

-- | Slots for child components
type Slots =
  ( diemTracker :: H.Slot DiemTracker.Query DiemTracker.Output Unit
  , tokenChart :: H.Slot TokenChart.Query TokenChart.Output Unit
  , costChart :: H.Slot CostChart.Query CostChart.Output Unit
  , sessionSummary :: H.Slot SessionSummary.Query Void Unit
  )

_diemTracker = Proxy :: Proxy "diemTracker"
_tokenChart = Proxy :: Proxy "tokenChart"
_costChart = Proxy :: Proxy "costChart"
_sessionSummary = Proxy :: Proxy "sessionSummary"

-- | Component state - Dashboard internal state
-- |
-- | **Purpose:** Stores the application state for rendering and countdown timer.
-- | **Invariant:** State is always equal to the Input.state (no local state mutations).
-- | **Note:** This component is stateless - state comes entirely from props.
type State =
  { appState :: AppState
  , countdown :: TimeRemaining
  , chartTimeRange :: TokenUsage.TimeRange
  }

-- | Component actions
data Action
  = Initialize
  | UpdateCountdown TimeRemaining
  | HandleDiemTrackerOutput DiemTracker.Output
  | HandleTokenChartOutput TokenChart.Output
  | HandleCostChartOutput CostChart.Output
  | SetChartTimeRange TokenUsage.TimeRange

-- | Component query - Dashboard component queries
-- |
-- | **Purpose:** Allows parent components to update the dashboard state.
-- | **Queries:**
-- | - `UpdateState newState`: Updates the dashboard to display newState
data Query a = UpdateState AppState a

-- | Dashboard component - Main dashboard component factory
-- |
-- | **Purpose:** Creates the dashboard component instance.
-- | **Returns:** A Halogen component that renders the dashboard view
-- | **Side Effects:** None (pure component creation)
component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState: \input -> 
      { appState: input.state
      , countdown: { hours: 0, minutes: 0, seconds: 0, totalMs: 0.0 }
      , chartTimeRange: TokenUsage.LastHour
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , initialize = Just Initialize
      }
  }

-- | Render function - Creates the dashboard HTML
-- |
-- | **Purpose:** Renders the dashboard view with DiemTracker widget, session, and proof widgets.
-- | **Parameters:**
-- | - `state`: The current application state to display
-- | **Returns:** Halogen HTML representing the dashboard
-- | **Side Effects:** None (pure rendering)
-- |
-- | **Rendering Structure:**
-- | - Outer container with "dashboard" class
-- | - Header with title and connection status
-- | - DiemTracker widget (pinned at top)
-- | - Content area containing session and proof widgets
render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ HP.classes [ H.ClassName "dashboard" ] ]
    [ renderHeader state
    , HH.div
        [ HP.class_ (H.ClassName "dashboard__diem-section") ]
        [ HH.slot _diemTracker unit DiemTracker.component
            { balance: state.appState.balance
            , countdown: state.countdown
            }
            HandleDiemTrackerOutput
        ]
    , HH.div
        [ HP.classes [ H.ClassName "dashboard__charts-row" ] ]
        [ HH.div
            [ HP.class_ (H.ClassName "dashboard__chart-card") ]
            [ renderTimeRangeSelector state.chartTimeRange
            , HH.slot _tokenChart unit TokenChart.component unit
                HandleTokenChartOutput
            ]
        ]
    , HH.div
        [ HP.classes [ H.ClassName "dashboard-content" ] ]
        [ renderSession state.appState.session
        , renderProof state.appState.proof
        ]
    , renderQuickStats state
    ]

-- | Render header with title and connection status
renderHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderHeader state =
  HH.header
    [ HP.class_ (H.ClassName "dashboard__header") ]
    [ HH.h1_ [ HH.text "Forge Sidepanel Dashboard" ]
    , HH.div
        [ HP.classes $ connectionClasses state.appState.connected ]
        [ HH.span 
            [ HP.class_ (H.ClassName "connection-indicator") ]
            []
        , HH.text $ if state.appState.connected then "Connected" else "Disconnected"
        ]
    ]

connectionClasses :: Boolean -> Array H.ClassName
connectionClasses connected =
  [ H.ClassName "connection-status" ] <>
  if connected 
    then [ H.ClassName "connection-status--connected" ]
    else [ H.ClassName "connection-status--disconnected" ]

-- Balance rendering is now handled by DiemTracker component

-- | Render session widget - Display current session information
-- |
-- | **Purpose:** Displays the current active session information, including model,
-- |             tokens, and cost.
-- | **Parameters:**
-- | - `session`: Optional session state (Nothing if no active session)
-- | **Returns:** Halogen HTML for the session widget
-- | **Side Effects:** None (pure rendering)
-- |
-- | **Displays:**
-- | - Model name
-- | - Total tokens used in session
-- | - Session cost
-- Session rendering is now handled by SessionSummary component

renderProof :: forall m. ProofState -> H.ComponentHTML Action Slots m
renderProof proof =
  HH.div
    [ HP.classes [ H.ClassName "proof-widget" ] ]
    [ HH.h2_ [ HH.text "Lean4 Proof Status" ]
    , HH.p_ [ HH.text $ "Connected: " <> show proof.connected ]
    , HH.p_ [ HH.text $ "Goals: " <> show (Array.length proof.goals) ]
    ]

-- | Render time range selector
renderTimeRangeSelector :: forall m. TokenUsage.TimeRange -> H.ComponentHTML Action Slots m
renderTimeRangeSelector current =
  HH.div
    [ HP.class_ (H.ClassName "time-range-selector") ]
    [ renderTimeRangeButton TokenUsage.LastHour "1h" current
    , renderTimeRangeButton TokenUsage.LastDay "24h" current
    , renderTimeRangeButton TokenUsage.LastWeek "7d" current
    , renderTimeRangeButton TokenUsage.AllTime "All" current
    ]

renderTimeRangeButton :: forall m. TokenUsage.TimeRange -> String -> TokenUsage.TimeRange -> H.ComponentHTML Action Slots m
renderTimeRangeButton range label current =
  HH.button
    [ HP.classes $ timeRangeButtonClasses (range == current)
    , HE.onClick \_ -> SetChartTimeRange range
    ]
    [ HH.text label ]

timeRangeButtonClasses :: Boolean -> Array H.ClassName
timeRangeButtonClasses selected =
  [ H.ClassName "time-range-button" ] <>
  if selected then [ H.ClassName "time-range-button--selected" ] else []

-- | Render quick stats footer
renderQuickStats :: forall m. State -> H.ComponentHTML Action Slots m
renderQuickStats state =
  HH.div
    [ HP.class_ (H.ClassName "dashboard__quick-stats") ]
    [ renderStat "Today" (formatDiem state.appState.balance.metrics.todayUsed)
    , renderStat "Avg Daily" (formatDiem state.appState.balance.metrics.averageDaily)
    , renderStat "Rate" (show state.appState.balance.metrics.consumptionRate <> "/hr")
    ]

renderStat :: forall m. String -> String -> H.ComponentHTML Action Slots m
renderStat label value =
  HH.div
    [ HP.class_ (H.ClassName "quick-stat") ]
    [ HH.span [ HP.class_ (H.ClassName "quick-stat__label") ] [ HH.text label ]
    , HH.span [ HP.class_ (H.ClassName "quick-stat__value") ] [ HH.text value ]
    ]

-- Cost breakdown calculation moved to TokenUsage.Utils module

-- | Handle component actions
handleAction :: forall m. MonadAff m => MonadEffect m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Initialize countdown timer
    countdown <- liftEffect getTimeUntilReset
    H.modify_ _ { countdown = countdown }
    
    -- Initialize charts with current data
    state <- H.get
    now <- liftEffect getCurrentDateTime
    let filteredSessions = TokenUsage.filterSessionsByTimeRange state.chartTimeRange state.appState.sessionHistory now
    let dataPoints = TokenUsage.sessionsToDataPoints filteredSessions
    void $ H.query _tokenChart unit $ H.request $ TokenChart.UpdateData dataPoints
    void $ H.query _costChart unit $ H.request $ CostChart.UpdateBreakdown (TokenUsage.calculateCostBreakdown state.appState.sessionHistory)
    
    -- Start countdown ticker (updates every second)
    -- Use same pattern as CountdownTimer component
    void $ H.subscribe $ H.Emitter \emit -> do
      fiber <- liftAff $ forkAff $ forever do
        delay (Milliseconds 1000.0)
        newCountdown <- liftEffect getTimeUntilReset
        liftEffect $ emit (UpdateCountdown newCountdown)
      pure $ killFiber (error "unsubscribed") fiber
  
  UpdateCountdown countdown ->
    H.modify_ _ { countdown = countdown }
  
  HandleDiemTrackerOutput output -> case output of
    DiemTracker.AlertTriggered alertLevel ->
      -- Could show notification or log
      pure unit
    DiemTracker.SettingsRequested ->
      -- Could navigate to settings
      pure unit
    DiemTracker.RefreshRequested ->
      -- Could trigger balance refresh
      pure unit
  
  HandleTokenChartOutput output -> case output of
    TokenChart.ChartReady ->
      -- Chart initialized successfully
      pure unit
    TokenChart.ChartError msg ->
      -- Could show error notification
      pure unit
  
  HandleCostChartOutput output -> case output of
    CostChart.ChartReady ->
      -- Chart initialized successfully
      pure unit
    CostChart.ChartError msg ->
      -- Could show error notification
      pure unit
  
  SetChartTimeRange range -> do
    H.modify_ _ { chartTimeRange = range }
    -- Update token chart with filtered data
    state <- H.get
    now <- liftEffect getCurrentDateTime
    let filteredSessions = TokenUsage.filterSessionsByTimeRange range state.appState.sessionHistory now
    let dataPoints = TokenUsage.sessionsToDataPoints filteredSessions
    void $ H.query _tokenChart unit $ H.request $ TokenChart.UpdateData dataPoints

-- | Handle component queries - Process queries from parent components
-- |
-- | **Purpose:** Processes queries from parent components, currently only handles state updates.
-- | **Parameters:**
-- | - `query`: The query to process (currently only UpdateState)
-- | **Returns:** Maybe a continuation value
-- | **Side Effects:** Updates component state via H.put
handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
handleQuery = case _ of
  UpdateState newState k -> do
    currentCountdown <- H.gets _.countdown
    currentTimeRange <- H.gets _.chartTimeRange
    H.modify_ _ { appState = newState, countdown = currentCountdown, chartTimeRange = currentTimeRange }
    -- Update token chart with filtered data
    now <- liftEffect getCurrentDateTime
    let filteredSessions = TokenUsage.filterSessionsByTimeRange currentTimeRange newState.sessionHistory now
    let dataPoints = TokenUsage.sessionsToDataPoints filteredSessions
    void $ H.query _tokenChart unit $ H.request $ TokenChart.UpdateData dataPoints
    -- Update cost breakdown chart
    void $ H.query _costChart unit $ H.request $ CostChart.UpdateBreakdown (TokenUsage.calculateCostBreakdown newState.sessionHistory)
    pure (Just k)
