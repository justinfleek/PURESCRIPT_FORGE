# 63-TIMELINE-VIEW: Time-Travel Debugging Interface

## Overview

The Timeline View enables time-travel debugging by visualizing state snapshots over time. Users can scrub through history, compare states, and restore previous points—a key differentiator for power users.

**Phase:** 3 (Advanced Features)

---

## Concept

### Why Time-Travel?

Senior engineers expect sophisticated debugging:
1. **"What did my context look like 30 minutes ago?"**
2. **"Compare current state to when it was working"**
3. **"Restore to before I made that change"**

The Timeline provides visual answers to these questions.

---

## Visual Design

### Timeline Layout

```
┌─────────────────────────────────────────────────────────────────────────┐
│  TIMELINE                                               [Create Snapshot]│
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  ┌───────────────────────────────────────────────────────────────────┐  │
│  │ ◄│                                                            │► │  │
│  │   ●━━━━━●━━━━━━━━━●━━━━●━━━━━━━━━━━━━━━━━━━●━━━━━●━━━━━━━━━━◉   │  │
│  │   │     │         │    │                   │     │          ▲   │  │
│  │  2:00  2:15      2:30 2:35               3:00  3:15       NOW   │  │
│  │                         ▲                                        │  │
│  │                   Selected                                       │  │
│  └───────────────────────────────────────────────────────────────────┘  │
│                                                                          │
│  SNAPSHOT DETAILS                                     2:35 PM            │
│  ────────────────────────────────────────────────────────────────────   │
│                                                                          │
│  ┌─────────────────────────────────┐ ┌─────────────────────────────────┐│
│  │  Balance                        │ │  Session                        ││
│  │  ◉ 45.2 Diem  (vs 42.5 now)    │ │  Messages: 8 (vs 12 now)       ││
│  │  +2.7 higher                    │ │  Tokens: 12,456 (vs 23,955)    ││
│  └─────────────────────────────────┘ └─────────────────────────────────┘│
│                                                                          │
│  ┌─────────────────────────────────┐ ┌─────────────────────────────────┐│
│  │  Context Files                  │ │  Proof State                    ││
│  │  • src/App.tsx                  │ │  Goals: 2 (vs 0 now)           ││
│  │  • src/utils.ts                 │ │  Diagnostics: 1 warning        ││
│  └─────────────────────────────────┘ └─────────────────────────────────┘│
│                                                                          │
│  [View Diff]                              [Restore to This Point]        │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

### Snapshot Markers

```
●  Regular snapshot (auto or manual)
◉  Current position (NOW)
◆  Manual snapshot (user-created)
⚠  Snapshot with warning state
✗  Snapshot with error
```

---

## PureScript Implementation

### Types

```purescript
module Sidepanel.Components.Timeline.TimelineView where

import Prelude
import Data.DateTime (DateTime)
import Data.Array (Array)
import Data.Maybe (Maybe)

-- Snapshot summary for timeline
type SnapshotSummary =
  { id :: String
  , timestamp :: DateTime
  , description :: Maybe String
  , isManual :: Boolean
  , hasWarning :: Boolean
  , hasError :: Boolean
  }

-- Full snapshot with state data
type Snapshot =
  { id :: String
  , timestamp :: DateTime
  , description :: Maybe String
  , state :: SnapshotState
  }

type SnapshotState =
  { balance :: BalanceSnapshot
  , session :: Maybe SessionSnapshot
  , proof :: ProofSnapshot
  , files :: Array FileContext
  }

type BalanceSnapshot =
  { diem :: Number
  , usd :: Number
  , effective :: Number
  }

type SessionSnapshot =
  { messageCount :: Int
  , promptTokens :: Int
  , completionTokens :: Int
  , cost :: Number
  }

type ProofSnapshot =
  { goalCount :: Int
  , diagnosticCount :: Int
  , hasErrors :: Boolean
  }

-- Component state
type State =
  { snapshots :: Array SnapshotSummary
  , selectedId :: Maybe String
  , selectedSnapshot :: Maybe Snapshot
  , currentState :: AppState  -- For comparison
  , isDragging :: Boolean
  , timeRange :: TimeRange
  }

data TimeRange = LastHour | Last6Hours | Last24Hours | AllTime

-- Actions
data Action
  = Initialize
  | LoadSnapshots
  | SelectSnapshot String
  | SnapshotLoaded Snapshot
  | CreateManualSnapshot String
  | RestoreSnapshot String
  | SetTimeRange TimeRange
  | HandleScrubStart
  | HandleScrubMove Number  -- Position 0-1
  | HandleScrubEnd

-- Outputs
data Output
  = SnapshotRestored String
  | SnapshotCreated String
```

### Timeline Scrubber Component

```purescript
module Sidepanel.Components.Timeline.Scrubber where

renderScrubber :: forall m. State -> H.ComponentHTML Action () m
renderScrubber state =
  HH.div
    [ HP.class_ (H.ClassName "timeline-scrubber")
    , HP.ref scrubberRef
    , HE.onMouseDown \_ -> HandleScrubStart
    , HE.onMouseMove handleMouseMove
    , HE.onMouseUp \_ -> HandleScrubEnd
    , HE.onMouseLeave \_ -> HandleScrubEnd
    ]
    [ -- Track
      HH.div [ HP.class_ (H.ClassName "scrubber__track") ] []
    
    -- Markers
    , HH.div
        [ HP.class_ (H.ClassName "scrubber__markers") ]
        (map (renderMarker state) state.snapshots)
    
    -- Playhead (current position)
    , HH.div
        [ HP.class_ (H.ClassName "scrubber__playhead")
        , HP.style $ "left: " <> show (playheadPosition state) <> "%"
        ]
        []
    
    -- Time labels
    , HH.div
        [ HP.class_ (H.ClassName "scrubber__labels") ]
        (renderTimeLabels state.timeRange)
    ]

renderMarker :: forall m. State -> SnapshotSummary -> H.ComponentHTML Action () m
renderMarker state snapshot =
  let
    position = calculatePosition snapshot.timestamp state
    isSelected = state.selectedId == Just snapshot.id
    markerClass = getMarkerClass snapshot isSelected
  in
    HH.div
      [ HP.classes [ H.ClassName "scrubber__marker", markerClass ]
      , HP.style $ "left: " <> show position <> "%"
      , HE.onClick \_ -> SelectSnapshot snapshot.id
      , HP.attr (H.AttrName "title") $ formatSnapshotTooltip snapshot
      ]
      []

getMarkerClass :: SnapshotSummary -> Boolean -> H.ClassName
getMarkerClass snapshot isSelected =
  H.ClassName $ case snapshot of
    _ | isSelected -> "marker--selected"
    { hasError: true } -> "marker--error"
    { hasWarning: true } -> "marker--warning"
    { isManual: true } -> "marker--manual"
    _ -> "marker--auto"

-- Calculate position (0-100%) based on timestamp
calculatePosition :: DateTime -> State -> Number
calculatePosition timestamp state =
  let
    range = getTimeRangeMs state.timeRange
    now = getCurrentTime
    snapshotMs = toMilliseconds timestamp
    startMs = toMilliseconds now - range
    
    position = (snapshotMs - startMs) / range * 100.0
  in
    clamp 0.0 100.0 position
```

### Snapshot Details Panel

```purescript
renderSnapshotDetails :: forall m. Snapshot -> AppState -> H.ComponentHTML Action () m
renderSnapshotDetails snapshot current =
  HH.div
    [ HP.class_ (H.ClassName "snapshot-details") ]
    [ HH.div
        [ HP.class_ (H.ClassName "snapshot-details__header") ]
        [ HH.span [ HP.class_ (H.ClassName "section-title") ] 
            [ HH.text "Snapshot Details" ]
        , HH.span [ HP.class_ (H.ClassName "snapshot-details__time") ] 
            [ HH.text $ formatDateTime snapshot.timestamp ]
        ]
    
    -- Comparison cards
    , HH.div
        [ HP.class_ (H.ClassName "snapshot-details__cards") ]
        [ renderComparisonCard "Balance" 
            (renderBalanceComparison snapshot.state.balance current.balance)
        , renderComparisonCard "Session"
            (renderSessionComparison snapshot.state.session current.session)
        , renderComparisonCard "Context Files"
            (renderFilesComparison snapshot.state.files)
        , renderComparisonCard "Proof State"
            (renderProofComparison snapshot.state.proof current.proof)
        ]
    
    -- Actions
    , HH.div
        [ HP.class_ (H.ClassName "snapshot-details__actions") ]
        [ HH.button
            [ HP.classes [ H.ClassName "btn", H.ClassName "btn--secondary" ]
            , HE.onClick \_ -> ViewDiff
            ]
            [ HH.text "View Diff" ]
        , HH.button
            [ HP.classes [ H.ClassName "btn", H.ClassName "btn--primary" ]
            , HE.onClick \_ -> RestoreSnapshot snapshot.id
            ]
            [ HH.text "Restore to This Point" ]
        ]
    ]

renderBalanceComparison :: forall m. BalanceSnapshot -> BalanceState -> H.ComponentHTML Action () m
renderBalanceComparison snapshot current =
  let diff = snapshot.diem - current.diem
  in
    HH.div_
      [ HH.div 
          [ HP.class_ (H.ClassName "comparison-value") ]
          [ HH.text $ "◉ " <> formatDiem snapshot.diem <> " Diem" ]
      , HH.div 
          [ HP.class_ (H.ClassName "comparison-current") ]
          [ HH.text $ "(vs " <> formatDiem current.diem <> " now)" ]
      , HH.div 
          [ HP.classes $ diffClasses diff ]
          [ HH.text $ formatDiff diff ]
      ]

diffClasses :: Number -> Array H.ClassName
diffClasses diff
  | diff > 0 = [ H.ClassName "diff", H.ClassName "diff--positive" ]
  | diff < 0 = [ H.ClassName "diff", H.ClassName "diff--negative" ]
  | otherwise = [ H.ClassName "diff", H.ClassName "diff--neutral" ]

formatDiff :: Number -> String
formatDiff diff
  | diff > 0 = "+" <> formatDiem diff <> " higher"
  | diff < 0 = formatDiem (abs diff) <> " lower"
  | otherwise = "unchanged"
```

---

## Snapshot Storage

### Database Schema

```sql
-- Snapshots table
CREATE TABLE snapshots (
  id TEXT PRIMARY KEY,
  timestamp TEXT NOT NULL,
  description TEXT,
  is_manual BOOLEAN DEFAULT FALSE,
  
  -- Serialized state (JSON)
  state_json TEXT NOT NULL,
  
  -- Quick-access fields for timeline display
  balance_diem REAL,
  session_message_count INTEGER,
  has_warning BOOLEAN DEFAULT FALSE,
  has_error BOOLEAN DEFAULT FALSE,
  
  created_at TEXT DEFAULT CURRENT_TIMESTAMP
);

CREATE INDEX idx_snapshots_timestamp ON snapshots(timestamp);
```

### Auto-Snapshot Strategy

```typescript
// Create snapshots automatically at key moments
class SnapshotManager {
  private lastSnapshotTime: Date = new Date(0);
  private readonly MIN_INTERVAL_MS = 5 * 60 * 1000;  // 5 minutes
  
  // Trigger conditions
  shouldCreateSnapshot(event: string, state: AppState): boolean {
    const now = Date.now();
    const timeSinceLast = now - this.lastSnapshotTime.getTime();
    
    // Always snapshot on manual trigger
    if (event === 'manual') return true;
    
    // Respect minimum interval
    if (timeSinceLast < this.MIN_INTERVAL_MS) return false;
    
    // Snapshot on significant events
    switch (event) {
      case 'session.created':
        return true;
      case 'message.completed':
        // Every 5 messages or significant token usage
        return state.session?.messageCount % 5 === 0 ||
               this.significantTokenIncrease(state);
      case 'proof.changed':
        // Goal state changed
        return true;
      case 'balance.low':
        // Balance dropped below threshold
        return state.balance.alertLevel !== 'normal';
      default:
        return false;
    }
  }
  
  async createSnapshot(
    description: string | null,
    isManual: boolean
  ): Promise<Snapshot> {
    const state = this.store.getState();
    
    const snapshot: Snapshot = {
      id: generateId(),
      timestamp: new Date(),
      description,
      state: {
        balance: {
          diem: state.balance.diem,
          usd: state.balance.usd,
          effective: state.balance.effective
        },
        session: state.session ? {
          messageCount: state.session.messages.length,
          promptTokens: state.session.promptTokens,
          completionTokens: state.session.completionTokens,
          cost: state.session.cost
        } : null,
        proof: {
          goalCount: state.proof.goals.length,
          diagnosticCount: state.proof.diagnostics.length,
          hasErrors: state.proof.diagnostics.some(d => d.severity === 'error')
        },
        files: state.contextFiles ?? []
      }
    };
    
    await this.db.insertSnapshot(snapshot);
    this.lastSnapshotTime = new Date();
    
    return snapshot;
  }
}
```

---

## CSS Styling

```css
.timeline-view {
  display: flex;
  flex-direction: column;
  height: 100%;
  padding: var(--space-4);
}

.timeline-scrubber {
  position: relative;
  height: 60px;
  margin: var(--space-4) 0;
  user-select: none;
}

.scrubber__track {
  position: absolute;
  top: 20px;
  left: 0;
  right: 0;
  height: 4px;
  background: var(--color-border-subtle);
  border-radius: 2px;
}

.scrubber__markers {
  position: absolute;
  top: 0;
  left: 0;
  right: 0;
  bottom: 0;
}

.scrubber__marker {
  position: absolute;
  top: 14px;
  width: 12px;
  height: 12px;
  margin-left: -6px;
  border-radius: 50%;
  background: var(--color-text-tertiary);
  cursor: pointer;
  transition: transform var(--transition-fast);
}

.scrubber__marker:hover {
  transform: scale(1.3);
}

.marker--selected {
  background: var(--color-primary);
  box-shadow: 0 0 0 3px var(--color-primary-dim);
}

.marker--manual {
  background: var(--color-info);
  border-radius: 2px;
  transform: rotate(45deg);
}

.marker--warning {
  background: var(--color-warning);
}

.marker--error {
  background: var(--color-error);
}

.scrubber__playhead {
  position: absolute;
  top: 8px;
  width: 2px;
  height: 28px;
  background: var(--color-primary);
  margin-left: -1px;
}

.scrubber__playhead::after {
  content: 'NOW';
  position: absolute;
  top: -20px;
  left: 50%;
  transform: translateX(-50%);
  font-size: 10px;
  color: var(--color-primary);
  font-weight: var(--font-weight-semibold);
}

.scrubber__labels {
  position: absolute;
  bottom: 0;
  left: 0;
  right: 0;
  display: flex;
  justify-content: space-between;
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
}

.snapshot-details__cards {
  display: grid;
  grid-template-columns: repeat(2, 1fr);
  gap: var(--space-3);
  margin: var(--space-4) 0;
}

.comparison-card {
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: 8px;
  padding: var(--space-3);
}

.comparison-card__title {
  font-size: var(--font-size-xs);
  color: var(--color-text-secondary);
  text-transform: uppercase;
  letter-spacing: var(--letter-spacing-wider);
  margin-bottom: var(--space-2);
}

.diff--positive {
  color: var(--color-success);
}

.diff--negative {
  color: var(--color-error);
}

.diff--neutral {
  color: var(--color-text-tertiary);
}
```

---

## Related Specifications

- `64-SNAPSHOT-MANAGEMENT.md` - Snapshot storage details
- `65-STATE-DIFF-VIEW.md` - Diff visualization
- `89-IMPLEMENTATION-ROADMAP.md` - Phase 3 timeline

---

*"The best debugger is one that lets you travel through time."*
