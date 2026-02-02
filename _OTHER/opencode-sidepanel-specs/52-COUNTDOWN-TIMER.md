# 52-COUNTDOWN-TIMER: Reset Countdown Component

## Overview

The Countdown Timer displays the time remaining until Diem balance resets at UTC midnight. It's a key visual element that creates awareness of the daily budget cycle.

---

## Component Design

### Visual States

**Normal (> 2 hours)**
```
┌──────────────────────────────────┐
│  Resets in 8h 23m 17s            │
└──────────────────────────────────┘
```

**Warning (< 2 hours)**
```
┌──────────────────────────────────┐
│  ⚠ Resets in 1h 45m 32s          │  (amber color)
└──────────────────────────────────┘
```

**Critical (< 30 minutes)**
```
┌──────────────────────────────────┐
│  ⚠ Resets in 12m 08s             │  (red, pulsing)
└──────────────────────────────────┘
```

**Final Minute**
```
┌──────────────────────────────────┐
│  Resets in 0:47                  │  (seconds only)
└──────────────────────────────────┘
```

---

## PureScript Implementation

### Types

```purescript
module Sidepanel.Components.Balance.Countdown where

import Prelude
import Data.Maybe (Maybe(..))
import Data.DateTime (DateTime)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Effect.Aff (Milliseconds(..))
import Effect.Aff as Aff
import Effect.Aff.Class (class MonadAff, liftAff)

-- Time remaining structure
type TimeRemaining =
  { hours :: Int
  , minutes :: Int
  , seconds :: Int
  , totalSeconds :: Int
  , totalMs :: Number
  }

-- Urgency levels for styling
data UrgencyLevel = Normal | Warning | Critical

derive instance eqUrgencyLevel :: Eq UrgencyLevel

-- Component input
type Input = 
  { timezone :: Maybe String  -- For tooltip display
  }

-- Component state
type State =
  { timeRemaining :: TimeRemaining
  , urgencyLevel :: UrgencyLevel
  , showTooltip :: Boolean
  }

-- Component actions
data Action
  = Initialize
  | Tick
  | ToggleTooltip Boolean

-- No output (purely display component)
type Output = Void
```

### Component Definition

```purescript
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

initialState :: Input -> State
initialState _ =
  { timeRemaining: { hours: 0, minutes: 0, seconds: 0, totalSeconds: 0, totalMs: 0.0 }
  , urgencyLevel: Normal
  , showTooltip: false
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.classes $ containerClasses state.urgencyLevel
    , HP.attr (H.AttrName "role") "timer"
    , HP.attr (H.AttrName "aria-live") "polite"
    , HP.attr (H.AttrName "aria-label") $ "Diem resets in " <> formatAccessible state.timeRemaining
    , HE.onMouseEnter \_ -> ToggleTooltip true
    , HE.onMouseLeave \_ -> ToggleTooltip false
    ]
    [ -- Urgency icon (warning/critical only)
      case state.urgencyLevel of
        Normal -> HH.text ""
        _ -> HH.span [ HP.class_ (H.ClassName "countdown__icon") ] [ HH.text "⚠" ]
    
    -- Label
    , HH.span 
        [ HP.class_ (H.ClassName "countdown__label") ]
        [ HH.text "Resets in " ]
    
    -- Time display
    , HH.span 
        [ HP.class_ (H.ClassName "countdown__time") ]
        [ HH.text $ formatTime state.timeRemaining ]
    
    -- Tooltip
    , when state.showTooltip (renderTooltip state)
    ]

renderTooltip :: forall m. State -> H.ComponentHTML Action () m
renderTooltip state =
  HH.div
    [ HP.class_ (H.ClassName "countdown__tooltip") ]
    [ HH.div_ [ HH.text "Midnight UTC (00:00:00)" ]
    , HH.div_ [ HH.text $ "Your time: " <> getLocalResetTime ]
    , HH.div_ [ HH.text $ formatVerbose state.timeRemaining ]
    ]

containerClasses :: UrgencyLevel -> Array H.ClassName
containerClasses level =
  [ H.ClassName "countdown" ] <> case level of
    Normal -> []
    Warning -> [ H.ClassName "countdown--warning" ]
    Critical -> [ H.ClassName "countdown--critical" ]
```

### Action Handling

```purescript
handleAction :: forall m. MonadAff m 
             => Action 
             -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Calculate initial time
    time <- H.liftEffect getTimeUntilReset
    let urgency = calculateUrgency time
    H.modify_ _ { timeRemaining = time, urgencyLevel = urgency }
    
    -- Start ticker subscription
    void $ H.subscribe tickerEmitter

  Tick -> do
    time <- H.liftEffect getTimeUntilReset
    let urgency = calculateUrgency time
    H.modify_ _ { timeRemaining = time, urgencyLevel = urgency }
    
    -- Check if we just crossed midnight
    when (time.totalSeconds <= 0) do
      -- Reset already occurred, recalculate for tomorrow
      H.liftAff $ Aff.delay (Milliseconds 100.0)
      newTime <- H.liftEffect getTimeUntilReset
      H.modify_ _ { timeRemaining = newTime }

  ToggleTooltip show ->
    H.modify_ _ { showTooltip = show }

-- Ticker that fires every second
tickerEmitter :: forall m. MonadAff m => H.Emitter m Action
tickerEmitter = H.Emitter \emit -> do
  fiber <- Aff.forkAff $ forever do
    Aff.delay (Milliseconds 1000.0)
    liftEffect $ emit Tick
  pure $ Aff.killFiber (error "unsubscribed") fiber
```

### Time Calculation

```purescript
module Sidepanel.Utils.Countdown where

import Prelude
import Effect (Effect)
import Data.DateTime (DateTime)
import Data.DateTime as DateTime
import Data.DateTime.Instant (Instant, unInstant, instant)
import Data.Time.Duration (Milliseconds(..))
import Effect.Now (now)

-- | Calculate time until next UTC midnight
getTimeUntilReset :: Effect TimeRemaining
getTimeUntilReset = do
  nowInstant <- now
  let 
    nowMs = unInstant nowInstant
    -- Calculate milliseconds until midnight UTC
    msUntilReset = calculateMsUntilMidnightUTC nowMs
    totalSeconds = floor (msUntilReset / 1000.0)
    hours = totalSeconds / 3600
    minutes = (totalSeconds `mod` 3600) / 60
    seconds = totalSeconds `mod` 60
  pure
    { hours
    , minutes
    , seconds
    , totalSeconds
    , totalMs: msUntilReset
    }

-- Foreign function to calculate UTC midnight
foreign import calculateMsUntilMidnightUTC :: Number -> Number
```

```javascript
// FFI implementation
export const calculateMsUntilMidnightUTC = (nowMs) => {
  const now = new Date(nowMs);
  const tomorrow = new Date(Date.UTC(
    now.getUTCFullYear(),
    now.getUTCMonth(),
    now.getUTCDate() + 1,
    0, 0, 0, 0
  ));
  return tomorrow.getTime() - nowMs;
};
```

### Formatting

```purescript
-- | Format time for display: "4h 23m 17s"
formatTime :: TimeRemaining -> String
formatTime { hours, minutes, seconds, totalSeconds }
  -- Final minute: show seconds only
  | totalSeconds < 60 = "0:" <> padZero seconds
  -- Under an hour: show minutes and seconds
  | hours == 0 = show minutes <> "m " <> padZero seconds <> "s"
  -- Normal: show all
  | otherwise = show hours <> "h " <> padZero minutes <> "m " <> padZero seconds <> "s"

-- | Format for accessibility
formatAccessible :: TimeRemaining -> String
formatAccessible { hours, minutes, seconds } =
  show hours <> " hours, " <> 
  show minutes <> " minutes, " <>
  show seconds <> " seconds"

-- | Verbose format for tooltip
formatVerbose :: TimeRemaining -> String  
formatVerbose { hours, minutes, seconds } =
  show hours <> " hours, " <>
  show minutes <> " minutes, " <>
  show seconds <> " seconds remaining"

-- | Pad single digits with zero
padZero :: Int -> String
padZero n = if n < 10 then "0" <> show n else show n

-- | Get local time of UTC midnight
getLocalResetTime :: String
getLocalResetTime = 
  -- Implementation uses JS Date interop
  -- Returns something like "7:00 PM EST"
  foreign import getLocalMidnightString :: Effect String
```

### Urgency Calculation

```purescript
-- | Determine urgency level based on time remaining
calculateUrgency :: TimeRemaining -> UrgencyLevel
calculateUrgency { totalSeconds }
  | totalSeconds < 30 * 60 = Critical   -- < 30 minutes
  | totalSeconds < 2 * 60 * 60 = Warning -- < 2 hours
  | otherwise = Normal
```

---

## CSS Styling

```css
.countdown {
  display: inline-flex;
  align-items: center;
  gap: var(--space-1);
  font-family: var(--font-mono);
  position: relative;
}

.countdown__label {
  font-size: var(--font-size-sm);
  color: var(--color-text-secondary);
}

.countdown__time {
  font-size: var(--font-size-base);
  font-weight: var(--font-weight-semibold);
  color: var(--color-text-primary);
  font-variant-numeric: tabular-nums;
  /* Prevent width jumping when digits change */
  min-width: 9ch;
}

.countdown__icon {
  font-size: var(--font-size-sm);
}

/* Warning state */
.countdown--warning .countdown__time,
.countdown--warning .countdown__icon {
  color: var(--color-warning);
}

/* Critical state */
.countdown--critical .countdown__time,
.countdown--critical .countdown__icon {
  color: var(--color-error);
}

.countdown--critical .countdown__time {
  animation: pulse 1s ease-in-out infinite;
}

@keyframes pulse {
  0%, 100% { opacity: 1; }
  50% { opacity: 0.7; }
}

/* Tooltip */
.countdown__tooltip {
  position: absolute;
  top: 100%;
  left: 50%;
  transform: translateX(-50%);
  margin-top: var(--space-2);
  padding: var(--space-2) var(--space-3);
  background: var(--color-bg-elevated);
  border: 1px solid var(--color-border-default);
  border-radius: 6px;
  box-shadow: 0 4px 12px rgba(0, 0, 0, 0.3);
  font-size: var(--font-size-sm);
  white-space: nowrap;
  z-index: 100;
}

.countdown__tooltip::before {
  content: '';
  position: absolute;
  top: -6px;
  left: 50%;
  transform: translateX(-50%);
  border-left: 6px solid transparent;
  border-right: 6px solid transparent;
  border-bottom: 6px solid var(--color-border-default);
}

.countdown__tooltip > div {
  padding: 2px 0;
  color: var(--color-text-secondary);
}

.countdown__tooltip > div:first-child {
  color: var(--color-text-primary);
  font-weight: var(--font-weight-medium);
}

/* Reduced motion */
@media (prefers-reduced-motion: reduce) {
  .countdown--critical .countdown__time {
    animation: none;
  }
}
```

---

## Testing

```purescript
module Test.Components.CountdownSpec where

import Prelude
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Sidepanel.Components.Balance.Countdown

spec :: Spec Unit
spec = describe "Countdown Component" do
  describe "formatTime" do
    it "formats full time correctly" do
      let time = { hours: 4, minutes: 23, seconds: 17, totalSeconds: 15797, totalMs: 0.0 }
      formatTime time `shouldEqual` "4h 23m 17s"
    
    it "pads single-digit minutes and seconds" do
      let time = { hours: 1, minutes: 5, seconds: 8, totalSeconds: 3908, totalMs: 0.0 }
      formatTime time `shouldEqual` "1h 05m 08s"
    
    it "shows only minutes and seconds under an hour" do
      let time = { hours: 0, minutes: 45, seconds: 30, totalSeconds: 2730, totalMs: 0.0 }
      formatTime time `shouldEqual` "45m 30s"
    
    it "shows only seconds in final minute" do
      let time = { hours: 0, minutes: 0, seconds: 47, totalSeconds: 47, totalMs: 0.0 }
      formatTime time `shouldEqual` "0:47"

  describe "calculateUrgency" do
    it "returns Critical under 30 minutes" do
      let time = { hours: 0, minutes: 25, seconds: 0, totalSeconds: 1500, totalMs: 0.0 }
      calculateUrgency time `shouldEqual` Critical
    
    it "returns Warning under 2 hours" do
      let time = { hours: 1, minutes: 30, seconds: 0, totalSeconds: 5400, totalMs: 0.0 }
      calculateUrgency time `shouldEqual` Warning
    
    it "returns Normal over 2 hours" do
      let time = { hours: 5, minutes: 0, seconds: 0, totalSeconds: 18000, totalMs: 0.0 }
      calculateUrgency time `shouldEqual` Normal
```

---

## Related Specifications

- `12-DIEM-RESET-COUNTDOWN.md` - Countdown logic details
- `51-DIEM-TRACKER-WIDGET.md` - Parent widget
- `47-THEMING.md` - Visual styling

---

*"Every second matters when you're counting down."*
