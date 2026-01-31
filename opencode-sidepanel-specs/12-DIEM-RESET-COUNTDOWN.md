# 12-DIEM-RESET-COUNTDOWN: UTC Midnight Countdown Implementation

## Overview

The Diem reset countdown is a core visual element showing time remaining until the daily balance refresh. This creates urgency and budget awareness while being a constant reminder of the Diem system's value.

**Reset Time:** 00:00:00 UTC (Midnight UTC) every day

---

## Calculation Algorithm

### Core Time Calculation

```typescript
/**
 * Calculate milliseconds until next Diem reset (midnight UTC)
 */
function getMillisecondsUntilReset(): number {
  const now = new Date();
  
  // Create midnight UTC for tomorrow
  const tomorrow = new Date(Date.UTC(
    now.getUTCFullYear(),
    now.getUTCMonth(),
    now.getUTCDate() + 1,  // Tomorrow
    0, 0, 0, 0             // 00:00:00.000 UTC
  ));
  
  return tomorrow.getTime() - now.getTime();
}

/**
 * Get structured time remaining
 */
interface TimeRemaining {
  hours: number;
  minutes: number;
  seconds: number;
  totalSeconds: number;
  totalMilliseconds: number;
}

function getTimeUntilReset(): TimeRemaining {
  const ms = getMillisecondsUntilReset();
  const totalSeconds = Math.floor(ms / 1000);
  
  const hours = Math.floor(totalSeconds / 3600);
  const minutes = Math.floor((totalSeconds % 3600) / 60);
  const seconds = totalSeconds % 60;
  
  return {
    hours,
    minutes,
    seconds,
    totalSeconds,
    totalMilliseconds: ms
  };
}
```

### PureScript Implementation

```purescript
module Sidepanel.Utils.Countdown where

import Prelude
import Data.DateTime (DateTime, diff)
import Data.DateTime.Instant (Instant, unInstant, fromDateTime)
import Data.Time.Duration (Milliseconds(..), Hours(..), Minutes(..), Seconds(..))
import Data.Int (floor, toNumber)
import Effect (Effect)
import Effect.Now (now)

type TimeRemaining =
  { hours :: Int
  , minutes :: Int
  , seconds :: Int
  , totalMs :: Number
  }

-- | Get next midnight UTC
getNextMidnightUTC :: Effect Instant
getNextMidnightUTC = do
  currentInstant <- now
  -- Implementation uses JS Date interop
  pure $ calculateNextMidnight currentInstant

-- | Calculate time until reset
getTimeUntilReset :: Effect TimeRemaining
getTimeUntilReset = do
  currentInstant <- now
  nextReset <- getNextMidnightUTC
  let 
    Milliseconds ms = diff nextReset currentInstant
    totalSeconds = floor (ms / 1000.0)
    hours = totalSeconds / 3600
    minutes = (totalSeconds `mod` 3600) / 60
    seconds = totalSeconds `mod` 60
  pure
    { hours
    , minutes
    , seconds
    , totalMs: ms
    }

-- | Format for display: "4h 23m 17s"
formatTimeRemaining :: TimeRemaining -> String
formatTimeRemaining { hours, minutes, seconds } =
  show hours <> "h " <> 
  padZero minutes <> "m " <> 
  padZero seconds <> "s"
  where
    padZero n = if n < 10 then "0" <> show n else show n
```

---

## Display Formats

### Format Options

```typescript
type CountdownFormat = 
  | 'full'      // "4h 23m 17s"
  | 'compact'   // "4:23:17"
  | 'colon'     // "04:23:17"
  | 'words'     // "4 hours, 23 minutes, 17 seconds"
  | 'relative'; // "in about 4 hours"

function formatCountdown(time: TimeRemaining, format: CountdownFormat): string {
  const { hours, minutes, seconds } = time;
  
  switch (format) {
    case 'full':
      return `${hours}h ${padZero(minutes)}m ${padZero(seconds)}s`;
    
    case 'compact':
      return `${hours}:${padZero(minutes)}:${padZero(seconds)}`;
    
    case 'colon':
      return `${padZero(hours)}:${padZero(minutes)}:${padZero(seconds)}`;
    
    case 'words':
      return formatWords(hours, minutes, seconds);
    
    case 'relative':
      return formatRelative(hours, minutes);
  }
}

function padZero(n: number): string {
  return n.toString().padStart(2, '0');
}

function formatWords(hours: number, minutes: number, seconds: number): string {
  const parts: string[] = [];
  
  if (hours > 0) {
    parts.push(`${hours} ${hours === 1 ? 'hour' : 'hours'}`);
  }
  if (minutes > 0) {
    parts.push(`${minutes} ${minutes === 1 ? 'minute' : 'minutes'}`);
  }
  if (seconds > 0 && hours === 0) {  // Only show seconds when < 1 hour
    parts.push(`${seconds} ${seconds === 1 ? 'second' : 'seconds'}`);
  }
  
  return parts.join(', ');
}

function formatRelative(hours: number, minutes: number): string {
  if (hours === 0) {
    if (minutes <= 1) return 'in less than a minute';
    if (minutes <= 5) return 'in a few minutes';
    return `in about ${minutes} minutes`;
  }
  if (hours === 1) {
    return minutes > 30 ? 'in about 2 hours' : 'in about an hour';
  }
  return `in about ${hours} hours`;
}
```

---

## Timer Component Architecture

### State Management

```typescript
interface CountdownState {
  // Current time remaining
  timeRemaining: TimeRemaining;
  
  // Display settings
  format: CountdownFormat;
  showSeconds: boolean;
  
  // Animation state
  isAnimating: boolean;
  urgencyLevel: 'normal' | 'warning' | 'critical';
  
  // Sync metadata
  lastSync: Date;
  drift: number;  // Milliseconds of detected drift
}
```

### Update Strategy

**Why not just use `setInterval`?**

`setInterval` drifts over time. For a countdown that runs continuously, we need drift correction.

```typescript
class CountdownTimer {
  private intervalId: number | null = null;
  private expectedTime: number = 0;
  
  start(onTick: (time: TimeRemaining) => void): void {
    // Initial calculation
    onTick(getTimeUntilReset());
    
    // Calculate when next second boundary is
    const now = Date.now();
    const msUntilNextSecond = 1000 - (now % 1000);
    
    // Start on second boundary for clean ticks
    setTimeout(() => {
      this.expectedTime = Date.now() + 1000;
      onTick(getTimeUntilReset());
      
      this.intervalId = setInterval(() => {
        const drift = Date.now() - this.expectedTime;
        
        // If drift is significant (> 100ms), recalculate
        if (Math.abs(drift) > 100) {
          console.warn(`Countdown drift detected: ${drift}ms`);
        }
        
        this.expectedTime += 1000;
        onTick(getTimeUntilReset());
      }, 1000);
    }, msUntilNextSecond);
  }
  
  stop(): void {
    if (this.intervalId !== null) {
      clearInterval(this.intervalId);
      this.intervalId = null;
    }
  }
}
```

### Halogen Component

```purescript
module Sidepanel.Component.Countdown where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Effect.Aff as Aff
import Effect.Aff.Class (class MonadAff)

type State =
  { timeRemaining :: TimeRemaining
  , format :: CountdownFormat
  , urgencyLevel :: UrgencyLevel
  }

data Action
  = Initialize
  | Tick
  | SetFormat CountdownFormat

data UrgencyLevel = Normal | Warning | Critical

derive instance eqUrgencyLevel :: Eq UrgencyLevel

countdown :: forall q i o m. MonadAff m => H.Component q i o m
countdown = H.mkComponent
  { initialState: \_ -> 
      { timeRemaining: { hours: 0, minutes: 0, seconds: 0, totalMs: 0.0 }
      , format: Full
      , urgencyLevel: Normal
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.classes $ urgencyClasses state.urgencyLevel ]
    [ HH.span
        [ HP.class_ (H.ClassName "countdown-label") ]
        [ HH.text "Resets in " ]
    , HH.span
        [ HP.class_ (H.ClassName "countdown-time") ]
        [ HH.text $ formatTimeRemaining state.timeRemaining ]
    ]

urgencyClasses :: UrgencyLevel -> Array H.ClassName
urgencyClasses = case _ of
  Normal -> [ H.ClassName "countdown", H.ClassName "countdown--normal" ]
  Warning -> [ H.ClassName "countdown", H.ClassName "countdown--warning" ]
  Critical -> [ H.ClassName "countdown", H.ClassName "countdown--critical" ]

handleAction :: forall o m. MonadAff m => Action -> H.HalogenM State Action () o m Unit
handleAction = case _ of
  Initialize -> do
    -- Start tick loop
    void $ H.subscribe $ tickSubscription
  
  Tick -> do
    time <- H.liftEffect getTimeUntilReset
    let urgency = calculateUrgency time
    H.modify_ _ { timeRemaining = time, urgencyLevel = urgency }
  
  SetFormat fmt ->
    H.modify_ _ { format = fmt }

-- Subscription that ticks every second
tickSubscription :: forall m. MonadAff m => H.Emitter m Action
tickSubscription = H.Emitter \emit -> do
  -- Emit Tick every second
  fiber <- Aff.forkAff $ forever do
    Aff.delay (Aff.Milliseconds 1000.0)
    H.liftEffect $ emit Tick
  pure $ Aff.killFiber (Aff.error "Unmounted") fiber
```

---

## Visual Design

### CSS Styling

```css
.countdown {
  font-family: 'JetBrains Mono', 'Fira Code', monospace;
  font-variant-numeric: tabular-nums;  /* Prevents width jumping */
  display: flex;
  align-items: center;
  gap: 0.5rem;
}

.countdown-label {
  color: var(--text-secondary);
  font-size: 0.875rem;
}

.countdown-time {
  font-size: 1.25rem;
  font-weight: 600;
  letter-spacing: 0.02em;
}

/* Normal state */
.countdown--normal .countdown-time {
  color: var(--text-primary);
}

/* Warning state (< 2 hours) */
.countdown--warning .countdown-time {
  color: var(--color-warning);
}

/* Critical state (< 30 minutes) */
.countdown--critical .countdown-time {
  color: var(--color-error);
  animation: pulse 1s ease-in-out infinite;
}

@keyframes pulse {
  0%, 100% { opacity: 1; }
  50% { opacity: 0.7; }
}

/* Prevent layout shift when digits change */
.countdown-time {
  min-width: 8ch;  /* "23h 59m 59s" */
}
```

### Dark Theme Variables

```css
:root {
  --text-primary: #e4e4e7;
  --text-secondary: #a1a1aa;
  --color-warning: #f59e0b;
  --color-error: #ef4444;
  --countdown-bg: rgba(0, 0, 0, 0.2);
}
```

---

## Urgency Levels

### Thresholds

```typescript
function calculateUrgency(time: TimeRemaining): UrgencyLevel {
  const { totalSeconds } = time;
  
  // Critical: Less than 30 minutes
  if (totalSeconds < 30 * 60) {
    return 'critical';
  }
  
  // Warning: Less than 2 hours
  if (totalSeconds < 2 * 60 * 60) {
    return 'warning';
  }
  
  return 'normal';
}
```

### Visual Behavior by Level

| Level | Color | Animation | Sound |
|-------|-------|-----------|-------|
| Normal | White/Gray | None | None |
| Warning | Amber/Yellow | None | Optional chime |
| Critical | Red | Pulse | Optional alert |

---

## Timezone Handling

### User Timezone Display

While Diem resets at UTC midnight, users want to know "when in my time?"

```typescript
interface ResetTimeDisplay {
  utc: string;         // "00:00 UTC"
  local: string;       // "7:00 PM EST"
  localDate: string;   // "Today" or "Tomorrow"
}

function getResetTimeDisplay(): ResetTimeDisplay {
  // Midnight UTC
  const resetUTC = new Date();
  resetUTC.setUTCHours(24, 0, 0, 0);
  
  const utc = 'Midnight UTC';
  
  // Convert to local
  const localTime = resetUTC.toLocaleTimeString('en-US', {
    hour: 'numeric',
    minute: '2-digit',
    timeZoneName: 'short'
  });
  
  // Is it today or tomorrow in local time?
  const now = new Date();
  const isToday = resetUTC.getDate() === now.getDate();
  const localDate = isToday ? 'Today' : 'Tomorrow';
  
  return { utc, local: localTime, localDate };
}

// Example output for user in EST (UTC-5):
// { utc: "Midnight UTC", local: "7:00 PM EST", localDate: "Today" }
```

### Tooltip Content

```typescript
function getCountdownTooltip(): string {
  const display = getResetTimeDisplay();
  const time = getTimeUntilReset();
  
  return `
Diem resets at ${display.utc}
(${display.local} ${display.localDate})

Time remaining: ${formatCountdown(time, 'words')}
  `.trim();
}
```

---

## Edge Cases

### Near Midnight

When approaching midnight, precision matters:

```typescript
function getHighPrecisionCountdown(): TimeRemaining {
  const ms = getMillisecondsUntilReset();
  
  if (ms < 60000) {  // Less than 1 minute
    // Show milliseconds for final countdown
    return {
      hours: 0,
      minutes: 0,
      seconds: Math.floor(ms / 1000),
      milliseconds: ms % 1000,
      totalMilliseconds: ms
    };
  }
  
  return getTimeUntilReset();
}

// Format for final minute: "0:47.328"
function formatFinalCountdown(time: TimeRemainingWithMs): string {
  const { seconds, milliseconds } = time;
  return `${seconds}.${milliseconds.toString().padStart(3, '0')}`;
}
```

### System Sleep/Wake

```typescript
// Detect when system wakes from sleep
document.addEventListener('visibilitychange', () => {
  if (document.visibilityState === 'visible') {
    // Recalculate immediately on wake
    const time = getTimeUntilReset();
    updateCountdownDisplay(time);
    
    // Check if reset occurred while asleep
    const lastKnownReset = localStorage.getItem('lastDiemReset');
    const todayReset = getStartOfDiemDay().toISOString();
    
    if (lastKnownReset !== todayReset) {
      // Reset occurred! Trigger balance refresh
      refreshBalance();
      localStorage.setItem('lastDiemReset', todayReset);
    }
  }
});
```

### Clock Skew

```typescript
// Periodically sync with server time to detect skew
async function checkClockSkew(): Promise<number> {
  const clientBefore = Date.now();
  
  const response = await fetch('/api/time');
  const serverTime = await response.json();
  
  const clientAfter = Date.now();
  const roundTrip = clientAfter - clientBefore;
  const serverTimestamp = new Date(serverTime.iso).getTime();
  
  // Estimated server time accounting for latency
  const adjustedServerTime = serverTimestamp + (roundTrip / 2);
  const skew = clientAfter - adjustedServerTime;
  
  if (Math.abs(skew) > 5000) {  // More than 5 seconds
    console.warn(`Clock skew detected: ${skew}ms`);
    // Could adjust countdown calculations
  }
  
  return skew;
}
```

---

## Testing

### Unit Tests

```typescript
describe('Countdown Timer', () => {
  describe('Time Calculation', () => {
    it('calculates correctly at noon UTC', () => {
      jest.useFakeTimers();
      // Set to Jan 15, 2026, 12:00:00 UTC
      jest.setSystemTime(new Date('2026-01-15T12:00:00Z'));
      
      const time = getTimeUntilReset();
      
      expect(time.hours).toBe(12);
      expect(time.minutes).toBe(0);
      expect(time.seconds).toBe(0);
    });
    
    it('calculates correctly near midnight', () => {
      jest.useFakeTimers();
      // Set to 23:59:30 UTC
      jest.setSystemTime(new Date('2026-01-15T23:59:30Z'));
      
      const time = getTimeUntilReset();
      
      expect(time.hours).toBe(0);
      expect(time.minutes).toBe(0);
      expect(time.seconds).toBe(30);
    });
  });
  
  describe('Urgency Levels', () => {
    it('returns critical when under 30 minutes', () => {
      const time = { hours: 0, minutes: 15, seconds: 0, totalSeconds: 900 };
      expect(calculateUrgency(time)).toBe('critical');
    });
    
    it('returns warning when under 2 hours', () => {
      const time = { hours: 1, minutes: 30, seconds: 0, totalSeconds: 5400 };
      expect(calculateUrgency(time)).toBe('warning');
    });
    
    it('returns normal when over 2 hours', () => {
      const time = { hours: 5, minutes: 0, seconds: 0, totalSeconds: 18000 };
      expect(calculateUrgency(time)).toBe('normal');
    });
  });
  
  describe('Format', () => {
    it('formats full correctly', () => {
      const time = { hours: 4, minutes: 23, seconds: 7, totalSeconds: 0 };
      expect(formatCountdown(time, 'full')).toBe('4h 23m 07s');
    });
    
    it('formats compact correctly', () => {
      const time = { hours: 4, minutes: 23, seconds: 7, totalSeconds: 0 };
      expect(formatCountdown(time, 'compact')).toBe('4:23:07');
    });
  });
});
```

---

## Related Specifications

- `11-DIEM-TRACKING.md` - Balance tracking implementation
- `52-COUNTDOWN-TIMER.md` - UI component details
- `47-THEMING.md` - Visual styling system

---

*"Every tick is a reminder: your tokens are finite, but your creativity is not."*
