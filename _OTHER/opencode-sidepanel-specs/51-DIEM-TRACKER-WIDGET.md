# 51-DIEM-TRACKER-WIDGET: Balance Display Component

## Overview

The Diem Tracker Widget is the most visible component in the sidepanel. It displays current balance, consumption rate, and countdown to reset. This component must be:

- **Always visible:** Pinned to top of sidepanel
- **Real-time:** Updates on every balance change
- **Informative:** Shows rate, projection, alerts
- **Compact:** Maximum information density

---

## Visual Design

### Layout Structure

```
┌─────────────────────────────────────────────────────────────┐
│  DIEM BALANCE                              Resets in 4h 23m │
│  ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━ │
│                                                             │
│  ◉ 42.50 Diem        +$10.00 USD        = $52.50 effective │
│                                                             │
│  ┌─────────────────┐  ┌─────────────────┐                  │
│  │ 📉 2.3/hr       │  │ ⏱ ~18h left     │                  │
│  │ consumption     │  │ at current rate │                  │
│  └─────────────────┘  └─────────────────┘                  │
│                                                             │
│  Today: 7.50 used │ ████████░░░░░░░░░░░░ │ 42.50 remaining │
└─────────────────────────────────────────────────────────────┘
```

### States

**Normal State:**
- White/gray text
- No animation
- Standard opacity

**Warning State (< 20% or < 2h remaining):**
- Amber/yellow accent
- Subtle pulse on countdown
- Warning icon visible

**Critical State (< 5% or < 30min remaining):**
- Red accent color
- Pulsing animation
- Alert sound (optional)

**Depleted State (0 balance):**
- Red background tint
- "DEPLETED" badge
- Countdown shows "Resets in X"

---

## Component Structure

### PureScript Definition

```purescript
module Sidepanel.Components.Balance.DiemTracker where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)
import Data.Maybe (Maybe(..))
import Sidepanel.State.Balance (BalanceState, BalanceMetrics)

-- | Component input
type Input =
  { balance :: BalanceState
  }

-- | Component output
data Output
  = AlertTriggered Alert
  | SettingsRequested

-- | Internal state
type State =
  { balance :: BalanceState
  , expanded :: Boolean
  , alertLevel :: AlertLevel
  , showTooltip :: Maybe TooltipTarget
  }

data AlertLevel = Normal | Warning | Critical | Depleted

derive instance eqAlertLevel :: Eq AlertLevel

-- | Internal actions
data Action
  = Initialize
  | ReceiveInput Input
  | ToggleExpanded
  | ShowTooltip TooltipTarget
  | HideTooltip
  | OpenSettings
  | Tick

data TooltipTarget
  = DiemTooltip
  | UsdTooltip
  | RateTooltip
  | ProjectionTooltip
  | ProgressTooltip

-- | Queries from parent
data Query a
  = GetAlertLevel (AlertLevel -> a)
  | ForceRefresh a

-- | Component definition
component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , receive = Just <<< ReceiveInput
      , initialize = Just Initialize
      }
  }

initialState :: Input -> State
initialState { balance } =
  { balance
  , expanded: false
  , alertLevel: calculateAlertLevel balance
  , showTooltip: Nothing
  }
```

### Render Function

```purescript
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.classes $ containerClasses state.alertLevel ]
    [ renderHeader state
    , renderBalances state
    , renderMetrics state
    , renderProgress state
    ]

containerClasses :: AlertLevel -> Array H.ClassName
containerClasses level = 
  [ H.ClassName "diem-tracker" ] <> case level of
    Normal -> []
    Warning -> [ H.ClassName "diem-tracker--warning" ]
    Critical -> [ H.ClassName "diem-tracker--critical" ]
    Depleted -> [ H.ClassName "diem-tracker--depleted" ]

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.div
    [ HP.class_ (H.ClassName "diem-tracker__header") ]
    [ HH.span
        [ HP.class_ (H.ClassName "diem-tracker__title") ]
        [ HH.text "DIEM BALANCE" ]
    , HH.span
        [ HP.class_ (H.ClassName "diem-tracker__countdown") ]
        [ HH.text $ "Resets in " <> formatCountdown state.balance.countdown ]
    ]

renderBalances :: forall m. State -> H.ComponentHTML Action () m
renderBalances state =
  HH.div
    [ HP.class_ (H.ClassName "diem-tracker__balances") ]
    [ -- Diem balance
      HH.div
        [ HP.class_ (H.ClassName "diem-tracker__diem")
        , HE.onMouseEnter \_ -> ShowTooltip DiemTooltip
        , HE.onMouseLeave \_ -> HideTooltip
        ]
        [ HH.span [ HP.class_ (H.ClassName "balance-icon") ] [ HH.text "◉" ]
        , HH.span [ HP.class_ (H.ClassName "balance-value") ] 
            [ HH.text $ formatDiem state.balance.diem ]
        , HH.span [ HP.class_ (H.ClassName "balance-label") ]
            [ HH.text " Diem" ]
        ]
    
    -- USD balance
    , HH.div
        [ HP.class_ (H.ClassName "diem-tracker__usd")
        , HE.onMouseEnter \_ -> ShowTooltip UsdTooltip
        , HE.onMouseLeave \_ -> HideTooltip
        ]
        [ HH.text $ "+$" <> formatCurrency state.balance.usd <> " USD" ]
    
    -- Effective total
    , HH.div
        [ HP.class_ (H.ClassName "diem-tracker__effective") ]
        [ HH.text $ "= $" <> formatCurrency state.balance.effective <> " effective" ]
    ]

renderMetrics :: forall m. State -> H.ComponentHTML Action () m
renderMetrics state =
  HH.div
    [ HP.class_ (H.ClassName "diem-tracker__metrics") ]
    [ -- Consumption rate
      HH.div
        [ HP.class_ (H.ClassName "metric-card")
        , HE.onMouseEnter \_ -> ShowTooltip RateTooltip
        , HE.onMouseLeave \_ -> HideTooltip
        ]
        [ HH.span [ HP.class_ (H.ClassName "metric-icon") ] [ HH.text "📉" ]
        , HH.span [ HP.class_ (H.ClassName "metric-value") ]
            [ HH.text $ formatRate state.balance.metrics.consumptionRate <> "/hr" ]
        , HH.span [ HP.class_ (H.ClassName "metric-label") ]
            [ HH.text "consumption" ]
        ]
    
    -- Time to depletion
    , HH.div
        [ HP.class_ (H.ClassName "metric-card")
        , HE.onMouseEnter \_ -> ShowTooltip ProjectionTooltip
        , HE.onMouseLeave \_ -> HideTooltip
        ]
        [ HH.span [ HP.class_ (H.ClassName "metric-icon") ] [ HH.text "⏱" ]
        , HH.span [ HP.class_ (H.ClassName "metric-value") ]
            [ HH.text $ formatTimeToDepletion state.balance.metrics.timeToDepletion ]
        , HH.span [ HP.class_ (H.ClassName "metric-label") ]
            [ HH.text "at current rate" ]
        ]
    ]

renderProgress :: forall m. State -> H.ComponentHTML Action () m
renderProgress state =
  let
    todayUsed = state.balance.metrics.todayUsed
    remaining = state.balance.diem
    total = todayUsed + remaining
    percentage = if total > 0.0 then (remaining / total) * 100.0 else 0.0
  in
    HH.div
      [ HP.class_ (H.ClassName "diem-tracker__progress")
      , HE.onMouseEnter \_ -> ShowTooltip ProgressTooltip
      , HE.onMouseLeave \_ -> HideTooltip
      ]
      [ HH.span [ HP.class_ (H.ClassName "progress-label-left") ]
          [ HH.text $ "Today: " <> formatDiem todayUsed <> " used" ]
      , HH.div
          [ HP.class_ (H.ClassName "progress-bar") ]
          [ HH.div
              [ HP.class_ (H.ClassName "progress-fill")
              , HP.style $ "width: " <> show percentage <> "%"
              ]
              []
          ]
      , HH.span [ HP.class_ (H.ClassName "progress-label-right") ]
          [ HH.text $ formatDiem remaining <> " remaining" ]
      ]
```

### Action Handlers

```purescript
handleAction :: forall m. MonadAff m 
             => Action 
             -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Start countdown ticker
    void $ H.subscribe countdownTicker
  
  ReceiveInput { balance } -> do
    let newAlertLevel = calculateAlertLevel balance
    oldState <- H.get
    
    -- Check if alert level changed
    when (newAlertLevel /= oldState.alertLevel) do
      case newAlertLevel of
        Warning -> H.raise $ AlertTriggered $ BalanceWarning balance.diem
        Critical -> H.raise $ AlertTriggered $ BalanceCritical balance.diem
        Depleted -> H.raise $ AlertTriggered $ BalanceDepleted
        Normal -> pure unit
    
    H.modify_ _ { balance = balance, alertLevel = newAlertLevel }
  
  ToggleExpanded ->
    H.modify_ \s -> s { expanded = not s.expanded }
  
  ShowTooltip target ->
    H.modify_ _ { showTooltip = Just target }
  
  HideTooltip ->
    H.modify_ _ { showTooltip = Nothing }
  
  OpenSettings ->
    H.raise SettingsRequested
  
  Tick ->
    H.modify_ \s -> s 
      { balance = s.balance 
          { countdown = tickCountdown s.balance.countdown }
      }

-- | Countdown ticker subscription
countdownTicker :: forall m. MonadAff m => HS.Emitter m Action
countdownTicker = HS.makeEmitter \push -> do
  intervalId <- liftEffect $ setInterval 1000 $ push Tick
  pure $ liftEffect $ clearInterval intervalId
```

---

## Styling

### CSS

```css
.diem-tracker {
  background: var(--surface-elevated);
  border-radius: 8px;
  padding: 16px;
  border: 1px solid var(--border-subtle);
  font-family: 'JetBrains Mono', monospace;
}

.diem-tracker--warning {
  border-color: var(--color-warning);
  background: linear-gradient(
    135deg,
    var(--surface-elevated) 0%,
    rgba(245, 158, 11, 0.1) 100%
  );
}

.diem-tracker--critical {
  border-color: var(--color-error);
  background: linear-gradient(
    135deg,
    var(--surface-elevated) 0%,
    rgba(239, 68, 68, 0.15) 100%
  );
  animation: critical-pulse 2s ease-in-out infinite;
}

.diem-tracker--depleted {
  border-color: var(--color-error);
  background: rgba(239, 68, 68, 0.2);
}

@keyframes critical-pulse {
  0%, 100% { opacity: 1; }
  50% { opacity: 0.85; }
}

.diem-tracker__header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  margin-bottom: 12px;
  padding-bottom: 8px;
  border-bottom: 1px solid var(--border-subtle);
}

.diem-tracker__title {
  font-size: 11px;
  font-weight: 600;
  letter-spacing: 0.05em;
  color: var(--text-secondary);
  text-transform: uppercase;
}

.diem-tracker__countdown {
  font-size: 13px;
  color: var(--text-secondary);
  font-variant-numeric: tabular-nums;
}

.diem-tracker__balances {
  display: flex;
  align-items: baseline;
  gap: 12px;
  margin-bottom: 16px;
  flex-wrap: wrap;
}

.diem-tracker__diem {
  display: flex;
  align-items: baseline;
  gap: 4px;
}

.balance-icon {
  color: var(--color-primary);
  font-size: 12px;
}

.balance-value {
  font-size: 28px;
  font-weight: 700;
  color: var(--text-primary);
  font-variant-numeric: tabular-nums;
}

.balance-label {
  font-size: 14px;
  color: var(--text-secondary);
}

.diem-tracker__usd {
  font-size: 14px;
  color: var(--text-secondary);
}

.diem-tracker__effective {
  font-size: 14px;
  color: var(--text-tertiary);
}

.diem-tracker__metrics {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 12px;
  margin-bottom: 16px;
}

.metric-card {
  background: var(--surface-default);
  border-radius: 6px;
  padding: 10px 12px;
  cursor: help;
  transition: background 0.15s ease;
}

.metric-card:hover {
  background: var(--surface-hover);
}

.metric-icon {
  font-size: 14px;
  margin-right: 6px;
}

.metric-value {
  font-size: 16px;
  font-weight: 600;
  color: var(--text-primary);
  display: block;
}

.metric-label {
  font-size: 11px;
  color: var(--text-tertiary);
  text-transform: uppercase;
  letter-spacing: 0.03em;
}

.diem-tracker__progress {
  display: grid;
  grid-template-columns: auto 1fr auto;
  gap: 8px;
  align-items: center;
  font-size: 12px;
  color: var(--text-secondary);
}

.progress-bar {
  height: 6px;
  background: var(--surface-default);
  border-radius: 3px;
  overflow: hidden;
}

.progress-fill {
  height: 100%;
  background: var(--color-primary);
  border-radius: 3px;
  transition: width 0.3s ease;
}

.diem-tracker--warning .progress-fill {
  background: var(--color-warning);
}

.diem-tracker--critical .progress-fill,
.diem-tracker--depleted .progress-fill {
  background: var(--color-error);
}
```

### CSS Variables (Dark Theme)

```css
:root {
  /* Surfaces */
  --surface-default: #1a1a1a;
  --surface-elevated: #242424;
  --surface-hover: #2a2a2a;
  
  /* Text */
  --text-primary: #e4e4e7;
  --text-secondary: #a1a1aa;
  --text-tertiary: #71717a;
  
  /* Borders */
  --border-subtle: #333333;
  
  /* Colors */
  --color-primary: #3b82f6;
  --color-warning: #f59e0b;
  --color-error: #ef4444;
  --color-success: #22c55e;
}
```

---

## Tooltips

### Tooltip Content

```purescript
getTooltipContent :: TooltipTarget -> BalanceState -> String
getTooltipContent target balance = case target of
  DiemTooltip ->
    """Diem Balance
    
Earned from staking VVV tokens.
Resets daily at midnight UTC.
1 Diem = $1 API credit."""

  UsdTooltip ->
    """USD Balance
    
Deposited funds that don't reset.
Used after Diem is depleted.
Current: $""" <> formatCurrency balance.usd

  RateTooltip ->
    """Consumption Rate
    
Average Diem spent per hour
based on last 60 minutes.

Current: """ <> formatRate balance.metrics.consumptionRate <> """/hr
Peak today: """ <> formatRate balance.metrics.peakHourly <> """/hr"""

  ProjectionTooltip ->
    let projection = balance.metrics.timeToDepletion in
    """Time to Depletion
    
Estimated time until Diem
reaches zero at current rate.

""" <> case projection of
      Nothing -> "Not depleting (rate is 0)"
      Just d -> "Projected: " <> formatDuration d

  ProgressTooltip ->
    """Today's Usage
    
Used: """ <> formatDiem balance.metrics.todayUsed <> """
Remaining: """ <> formatDiem balance.diem <> """
Daily average: """ <> formatDiem balance.metrics.averageDaily
```

---

## Alert Logic

```purescript
calculateAlertLevel :: BalanceState -> AlertLevel
calculateAlertLevel balance
  | balance.diem <= 0.0 = Depleted
  | balance.diem < 1.0 = Critical  -- Less than 1 Diem
  | isTimeCritical balance = Critical
  | balance.diem < 5.0 = Warning  -- Less than 5 Diem
  | isTimeWarning balance = Warning
  | otherwise = Normal

isTimeCritical :: BalanceState -> Boolean
isTimeCritical balance = case balance.metrics.timeToDepletion of
  Nothing -> false
  Just duration -> duration.totalMinutes < 30.0

isTimeWarning :: BalanceState -> Boolean
isTimeWarning balance = case balance.metrics.timeToDepletion of
  Nothing -> false
  Just duration -> duration.totalMinutes < 120.0  -- 2 hours
```

---

## Accessibility

### ARIA Attributes

```purescript
renderBalances state =
  HH.div
    [ HP.class_ (H.ClassName "diem-tracker__balances")
    , HP.attr (H.AttrName "role") "status"
    , HP.attr (H.AttrName "aria-live") "polite"
    , HP.attr (H.AttrName "aria-label") $ 
        "Diem balance: " <> formatDiem state.balance.diem <>
        ", resets in " <> formatCountdown state.balance.countdown
    ]
    [ ... ]
```

### Keyboard Navigation

```purescript
-- Widget is focusable and expandable via keyboard
containerProps state =
  [ HP.tabIndex 0
  , HE.onKeyDown \event -> case eventKey event of
      "Enter" -> Just ToggleExpanded
      " " -> Just ToggleExpanded
      "s" -> Just OpenSettings
      _ -> Nothing
  ]
```

---

## Testing

### Unit Tests

```purescript
spec :: Spec Unit
spec = describe "DiemTracker" do
  describe "Alert Levels" do
    it "shows critical when balance is 0" do
      let balance = { diem: 0.0, usd: 10.0, metrics: defaultMetrics }
      calculateAlertLevel balance `shouldEqual` Depleted
    
    it "shows critical when under 30 minutes" do
      let metrics = defaultMetrics { timeToDepletion = Just (minutes 25) }
      let balance = { diem: 5.0, usd: 0.0, metrics }
      calculateAlertLevel balance `shouldEqual` Critical
    
    it "shows warning when under 2 hours" do
      let metrics = defaultMetrics { timeToDepletion = Just (hours 1) }
      let balance = { diem: 10.0, usd: 0.0, metrics }
      calculateAlertLevel balance `shouldEqual` Warning
    
    it "shows normal with healthy balance" do
      let metrics = defaultMetrics { timeToDepletion = Just (hours 10) }
      let balance = { diem: 50.0, usd: 0.0, metrics }
      calculateAlertLevel balance `shouldEqual` Normal

  describe "Formatting" do
    it "formats Diem with 2 decimal places" do
      formatDiem 42.5 `shouldEqual` "42.50"
    
    it "formats rate per hour" do
      formatRate 2.345 `shouldEqual` "2.3"
```

---

## Related Specifications

- `11-DIEM-TRACKING.md` - Balance tracking logic
- `12-DIEM-RESET-COUNTDOWN.md` - Countdown implementation
- `52-COUNTDOWN-TIMER.md` - Countdown component
- `47-THEMING.md` - Theme system

---

*"The balance widget is the heartbeat monitor. If it's not visible, the user is flying blind."*
