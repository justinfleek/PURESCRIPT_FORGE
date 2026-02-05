# 50-DASHBOARD-LAYOUT: Main Dashboard Composition

## Overview

The Dashboard is the default view when opening the sidepanel. It provides an at-a-glance overview of balance, usage, and session status, with navigation to detailed views.

---

## Layout Structure

### Desktop Layout (≥ 768px)

```
┌──────────────────────────────────────────────────────────────────────────┐
│  ┌─────────┐                                                             │
│  │ SIDEBAR │                    MAIN CONTENT                             │
│  │         │  ┌─────────────────────────────────────────────────────────┐│
│  │ 📊 Dash │  │  DIEM TRACKER                          Resets in 4h 23m ││
│  │ 💬 Sess │  │  ◉ 42.50 Diem + $10.00 USD = $52.50 effective           ││
│  │ 🔬 Proof│  │  📉 2.3/hr consumption    ⏱ ~18h left                   ││
│  │ ⏱ Time │  │  ████████░░░░░░░░░░░░ 42.50 remaining                   ││
│  │ ⚙ Set  │  └─────────────────────────────────────────────────────────┘│
│  │         │  ┌──────────────────────┐ ┌──────────────────────┐         │
│  │         │  │  TOKEN USAGE         │ │  COST BREAKDOWN      │         │
│  │         │  │  [Line Chart]        │ │  [Pie Chart]         │         │
│  │         │  │                      │ │                      │         │
│  │         │  │                      │ │                      │         │
│  │         │  └──────────────────────┘ └──────────────────────┘         │
│  │         │  ┌─────────────────────────────────────────────────────────┐│
│  │         │  │  CURRENT SESSION                                        ││
│  │         │  │  Model: llama-3.3-70b  │  Messages: 12  │  Cost: $0.014 ││
│  │         │  │  Tokens: 15,234 in / 8,721 out                          ││
│  └─────────┘  └─────────────────────────────────────────────────────────┘│
└──────────────────────────────────────────────────────────────────────────┘
```

### Mobile Layout (< 768px)

```
┌────────────────────────────────┐
│  ☰  OpenCode Sidepanel        │
├────────────────────────────────┤
│  DIEM TRACKER                  │
│  ◉ 42.50 Diem    4h 23m       │
│  ████████░░░░░░░░              │
├────────────────────────────────┤
│  [Token Usage Chart]           │
│                                │
├────────────────────────────────┤
│  [Current Session]             │
│  llama-3.3-70b  │  $0.014     │
├────────────────────────────────┤
│  📊    💬    🔬    ⏱    ⚙    │
└────────────────────────────────┘
```

---

## Component Hierarchy

```
Dashboard
├── Header
│   ├── ConnectionStatus
│   └── QuickActions
│
├── DiemTracker (pinned)
│   ├── BalanceDisplay
│   ├── Countdown
│   ├── MetricsCards
│   └── ProgressBar
│
├── ChartRow
│   ├── TokenUsageChart
│   │   ├── LineChart
│   │   └── TimeRangeSelector
│   │
│   └── CostBreakdownChart
│       └── PieChart
│
├── SessionSummary
│   ├── ModelInfo
│   ├── TokenCounts
│   └── CostDisplay
│
└── QuickStats
    ├── TodayUsage
    ├── AverageDaily
    └── ProjectedUsage
```

---

## PureScript Implementation

### Dashboard Component

```purescript
module Sidepanel.Components.Dashboard where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Effect.Aff.Class (class MonadAff)
import Type.Proxy (Proxy(..))

import Sidepanel.Components.Balance.DiemTracker as DiemTracker
import Sidepanel.Components.Usage.TokenChart as TokenChart
import Sidepanel.Components.Usage.CostBreakdown as CostBreakdown
import Sidepanel.Components.Session.SessionSummary as SessionSummary
import Sidepanel.State.AppState (AppState)

-- Slots for child components
type Slots =
  ( diemTracker :: H.Slot DiemTracker.Query DiemTracker.Output Unit
  , tokenChart :: H.Slot TokenChart.Query Void Unit
  , costBreakdown :: H.Slot CostBreakdown.Query Void Unit
  , sessionSummary :: H.Slot SessionSummary.Query Void Unit
  )

_diemTracker = Proxy :: Proxy "diemTracker"
_tokenChart = Proxy :: Proxy "tokenChart"
_costBreakdown = Proxy :: Proxy "costBreakdown"
_sessionSummary = Proxy :: Proxy "sessionSummary"

-- State
type State =
  { appState :: AppState
  , chartTimeRange :: TimeRange
  }

data TimeRange = LastHour | LastDay | LastWeek | AllTime

-- Actions
data Action
  = Initialize
  | UpdateFromStore AppState
  | HandleDiemTrackerOutput DiemTracker.Output
  | SetChartTimeRange TimeRange
  | Refresh

-- Component definition
component :: forall q i o m. MonadAff m => MonadStore m => H.Component q i o m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

initialState :: forall i. i -> State
initialState _ =
  { appState: initialAppState
  , chartTimeRange: LastHour
  }

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ HP.class_ (H.ClassName "dashboard") ]
    [ -- Connection status header
      renderHeader state
    
    -- Diem tracker (always visible at top)
    , HH.div
        [ HP.class_ (H.ClassName "dashboard__diem-section") ]
        [ HH.slot _diemTracker unit DiemTracker.component
            { balance: state.appState.balance }
            HandleDiemTrackerOutput
        ]
    
    -- Charts row
    , HH.div
        [ HP.class_ (H.ClassName "dashboard__charts-row") ]
        [ HH.div
            [ HP.class_ (H.ClassName "dashboard__chart-card") ]
            [ renderTimeRangeSelector state.chartTimeRange
            , HH.slot_ _tokenChart unit TokenChart.component
                { usage: state.appState.session.tokenHistory
                , timeRange: state.chartTimeRange
                }
            ]
        , HH.div
            [ HP.class_ (H.ClassName "dashboard__chart-card") ]
            [ HH.slot_ _costBreakdown unit CostBreakdown.component
                { breakdown: state.appState.session.costByModel }
            ]
        ]
    
    -- Session summary
    , HH.div
        [ HP.class_ (H.ClassName "dashboard__session-section") ]
        [ HH.slot_ _sessionSummary unit SessionSummary.component
            { session: state.appState.session }
        ]
    
    -- Quick stats footer
    , renderQuickStats state
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action Slots m
renderHeader state =
  HH.header
    [ HP.class_ (H.ClassName "dashboard__header") ]
    [ HH.div
        [ HP.class_ (H.ClassName "dashboard__title") ]
        [ HH.text "Dashboard" ]
    , HH.div
        [ HP.classes $ connectionClasses state.appState.connected ]
        [ HH.span 
            [ HP.class_ (H.ClassName "connection-indicator") ]
            []
        , HH.text $ if state.appState.connected then "Connected" else "Disconnected"
        ]
    ]

renderTimeRangeSelector :: forall m. TimeRange -> H.ComponentHTML Action Slots m
renderTimeRangeSelector current =
  HH.div
    [ HP.class_ (H.ClassName "time-range-selector") ]
    [ renderTimeRangeButton LastHour "1h" current
    , renderTimeRangeButton LastDay "24h" current
    , renderTimeRangeButton LastWeek "7d" current
    , renderTimeRangeButton AllTime "All" current
    ]

renderTimeRangeButton :: forall m. TimeRange -> String -> TimeRange -> H.ComponentHTML Action Slots m
renderTimeRangeButton range label current =
  HH.button
    [ HP.classes $ timeRangeButtonClasses (range == current)
    , HE.onClick \_ -> SetChartTimeRange range
    ]
    [ HH.text label ]

renderQuickStats :: forall m. State -> H.ComponentHTML Action Slots m
renderQuickStats state =
  HH.div
    [ HP.class_ (H.ClassName "dashboard__quick-stats") ]
    [ renderStat "Today" (formatDiem state.appState.balance.metrics.todayUsed)
    , renderStat "Avg Daily" (formatDiem state.appState.balance.metrics.averageDaily)
    , renderStat "Rate" (formatRate state.appState.balance.metrics.consumptionRate <> "/hr")
    ]

renderStat :: forall m. String -> String -> H.ComponentHTML Action Slots m
renderStat label value =
  HH.div
    [ HP.class_ (H.ClassName "quick-stat") ]
    [ HH.span [ HP.class_ (H.ClassName "quick-stat__label") ] [ HH.text label ]
    , HH.span [ HP.class_ (H.ClassName "quick-stat__value") ] [ HH.text value ]
    ]

connectionClasses :: Boolean -> Array H.ClassName
connectionClasses connected =
  [ H.ClassName "connection-status" ] <>
  if connected 
    then [ H.ClassName "connection-status--connected" ]
    else [ H.ClassName "connection-status--disconnected" ]

timeRangeButtonClasses :: Boolean -> Array H.ClassName
timeRangeButtonClasses selected =
  [ H.ClassName "time-range-button" ] <>
  if selected then [ H.ClassName "time-range-button--selected" ] else []
```

### Action Handlers

```purescript
handleAction :: forall o m. MonadAff m => MonadStore m 
             => Action -> H.HalogenM State Action Slots o m Unit
handleAction = case _ of
  Initialize -> do
    -- Subscribe to store updates
    subscribe \state -> UpdateFromStore state
    
    -- Get initial state
    state <- getState
    H.modify_ _ { appState = state }
  
  UpdateFromStore appState ->
    H.modify_ _ { appState = appState }
  
  HandleDiemTrackerOutput output -> case output of
    DiemTracker.AlertTriggered alert ->
      -- Could show notification, log, etc.
      pure unit
    DiemTracker.SettingsRequested ->
      -- Navigate to settings
      H.raise (Navigate Settings)
  
  SetChartTimeRange range ->
    H.modify_ _ { chartTimeRange = range }
  
  Refresh -> do
    -- Trigger balance refresh via WebSocket
    sendMessage { method: "balance.refresh", params: {} }
```

---

## CSS Styling

```css
.dashboard {
  display: flex;
  flex-direction: column;
  gap: var(--space-4);
  padding: var(--space-4);
  height: 100%;
  overflow-y: auto;
}

.dashboard__header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding-bottom: var(--space-3);
  border-bottom: 1px solid var(--color-border-subtle);
}

.dashboard__title {
  font-family: var(--font-mono);
  font-size: var(--font-size-lg);
  font-weight: var(--font-weight-semibold);
  color: var(--color-text-primary);
}

.connection-status {
  display: flex;
  align-items: center;
  gap: var(--space-2);
  font-size: var(--font-size-sm);
}

.connection-indicator {
  width: 8px;
  height: 8px;
  border-radius: 50%;
}

.connection-status--connected .connection-indicator {
  background: var(--color-success);
  box-shadow: 0 0 8px var(--color-success);
}

.connection-status--disconnected .connection-indicator {
  background: var(--color-error);
}

.dashboard__diem-section {
  /* DiemTracker is sticky at top when scrolling */
  position: sticky;
  top: 0;
  z-index: 10;
  background: var(--color-bg-base);
  padding-bottom: var(--space-3);
}

.dashboard__charts-row {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: var(--space-4);
}

@media (max-width: 768px) {
  .dashboard__charts-row {
    grid-template-columns: 1fr;
  }
}

.dashboard__chart-card {
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: var(--card-border-radius);
  padding: var(--space-4);
}

.dashboard__session-section {
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: var(--card-border-radius);
  padding: var(--space-4);
}

.dashboard__quick-stats {
  display: flex;
  justify-content: space-around;
  padding: var(--space-3);
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: var(--card-border-radius);
}

.quick-stat {
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: var(--space-1);
}

.quick-stat__label {
  font-size: var(--font-size-xs);
  color: var(--color-text-secondary);
  text-transform: uppercase;
  letter-spacing: var(--letter-spacing-wider);
}

.quick-stat__value {
  font-family: var(--font-mono);
  font-size: var(--font-size-lg);
  font-weight: var(--font-weight-semibold);
  color: var(--color-text-primary);
  font-variant-numeric: tabular-nums;
}

.time-range-selector {
  display: flex;
  gap: var(--space-1);
  margin-bottom: var(--space-3);
}

.time-range-button {
  padding: var(--space-1) var(--space-2);
  background: transparent;
  border: 1px solid var(--color-border-subtle);
  border-radius: 4px;
  font-family: var(--font-mono);
  font-size: var(--font-size-xs);
  color: var(--color-text-secondary);
  cursor: pointer;
  transition: all var(--transition-fast);
}

.time-range-button:hover {
  border-color: var(--color-border-default);
  color: var(--color-text-primary);
}

.time-range-button--selected {
  background: var(--color-primary-dim);
  border-color: var(--color-primary);
  color: var(--color-primary);
}
```

---

## Responsive Behavior

### Breakpoints

| Breakpoint | Width | Layout |
|------------|-------|--------|
| Mobile | < 640px | Single column, stacked |
| Tablet | 640-1024px | Two columns for charts |
| Desktop | > 1024px | Full layout with sidebar |

### Mobile Adaptations

1. **Collapsed sidebar** - Hamburger menu
2. **Stacked charts** - One per row
3. **Compact DiemTracker** - Condensed info
4. **Bottom navigation** - Tab bar instead of sidebar

---

## Data Flow

```
WebSocket ──► Store ──► Dashboard ──► Child Components
                │
                └──► Re-render on state change

User Action ──► Component ──► Store.update() ──► Broadcast
                   │
                   └──► WebSocket (if needed)
```

---

## Related Specifications

- `51-DIEM-TRACKER-WIDGET.md` - Balance display
- `53-TOKEN-USAGE-CHART.md` - Token visualization
- `40-PURESCRIPT-ARCHITECTURE.md` - Component patterns
- `47-THEMING.md` - Visual styling

---

*"The dashboard is the first thing users see. Make it count."*
