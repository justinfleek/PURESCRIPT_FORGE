# 56-ALERT-SYSTEM: Notifications and Warnings

## Overview

The Alert System provides visual and optional audio notifications for important events like low balance, rate limits, proof errors, and connection issues.

---

## Alert Types

### Alert Categories

| Category | Icon | Color | Sound | Examples |
|----------|------|-------|-------|----------|
| Balance | ◉ | Purple | Optional | Low Diem, depleted |
| Rate Limit | ⚡ | Orange | No | Approaching limit, limited |
| Connection | 🔌 | Red/Green | No | Disconnected, reconnected |
| Proof | 🔬 | Blue/Red | No | Goal solved, error |
| System | ⚠ | Yellow | Optional | Update available, error |

### Alert Levels

| Level | Persistence | Animation | Use Case |
|-------|-------------|-----------|----------|
| Info | 5s auto-dismiss | None | Informational |
| Warning | 10s auto-dismiss | Gentle pulse | Needs attention soon |
| Critical | Manual dismiss | Strong pulse | Immediate action needed |
| Success | 3s auto-dismiss | None | Positive confirmation |

---

## Visual Design

### Toast Notifications

```
┌─────────────────────────────────────────────────────────────┐
│  ⚠ Low Diem Balance                                    ✕   │
│  Only 5.2 Diem remaining (~2h at current rate)             │
│  ────────────────────────────────────────────────────────   │
│  [Dismiss]                              [View Dashboard]    │
└─────────────────────────────────────────────────────────────┘
```

### Inline Alerts

```
┌─────────────────────────────────────────────────────────────┐
│  ⚡ Rate Limited                                            │
│  Request limit reached. Retrying in 30s...                 │
└─────────────────────────────────────────────────────────────┘
```

### Badge Alerts (on sidebar icons)

```
┌───┐
│ 📊│
│ 💬│
│🔬⚠│  ← Warning badge
│ ⏱ │
└───┘
```

---

## PureScript Implementation

### Types

```purescript
module Sidepanel.Components.Alert where

import Prelude
import Data.DateTime (DateTime)
import Data.Maybe (Maybe)
import Data.UUID (UUID)

-- Alert definition
type Alert =
  { id :: UUID
  , category :: AlertCategory
  , level :: AlertLevel
  , title :: String
  , message :: String
  , timestamp :: DateTime
  , action :: Maybe AlertAction
  , dismissable :: Boolean
  , autoDismissMs :: Maybe Int
  }

data AlertCategory
  = BalanceAlert
  | RateLimitAlert
  | ConnectionAlert
  | ProofAlert
  | SystemAlert

data AlertLevel
  = Info
  | Warning
  | Critical
  | Success

type AlertAction =
  { label :: String
  , onClick :: Effect Unit
  }

-- Component state
type State =
  { alerts :: Array Alert
  , maxVisible :: Int
  , soundEnabled :: Boolean
  }

-- Actions
data Action
  = AddAlert Alert
  | DismissAlert UUID
  | DismissAll
  | ClearExpired
  | SetSoundEnabled Boolean

-- Global alert context
type AlertContext =
  { addAlert :: Alert -> Effect Unit
  , dismissAlert :: UUID -> Effect Unit
  , alerts :: Array Alert
  }
```

### Alert Container Component

```purescript
module Sidepanel.Components.AlertContainer where

component :: forall q m. MonadAff m => H.Component q Unit Void m
component = H.mkComponent
  { initialState: const initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

initialState :: State
initialState =
  { alerts: []
  , maxVisible: 5
  , soundEnabled: false
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "alert-container")
    , HP.attr (H.AttrName "role") "alert"
    , HP.attr (H.AttrName "aria-live") "polite"
    ]
    (map renderAlert $ take state.maxVisible state.alerts)

renderAlert :: forall m. Alert -> H.ComponentHTML Action () m
renderAlert alert =
  HH.div
    [ HP.classes $ alertClasses alert
    , HP.attr (H.AttrName "role") "alertdialog"
    ]
    [ -- Icon
      HH.div
        [ HP.class_ (H.ClassName "alert__icon") ]
        [ HH.text $ categoryIcon alert.category ]
    
    -- Content
    , HH.div
        [ HP.class_ (H.ClassName "alert__content") ]
        [ HH.div [ HP.class_ (H.ClassName "alert__title") ] [ HH.text alert.title ]
        , HH.div [ HP.class_ (H.ClassName "alert__message") ] [ HH.text alert.message ]
        ]
    
    -- Dismiss button
    , when alert.dismissable $
        HH.button
          [ HP.class_ (H.ClassName "alert__dismiss")
          , HP.attr (H.AttrName "aria-label") "Dismiss"
          , HE.onClick \_ -> DismissAlert alert.id
          ]
          [ HH.text "✕" ]
    
    -- Action button (if present)
    , case alert.action of
        Just action ->
          HH.button
            [ HP.class_ (H.ClassName "alert__action")
            , HE.onClick \_ -> do
                H.liftEffect action.onClick
                DismissAlert alert.id
            ]
            [ HH.text action.label ]
        Nothing -> HH.text ""
    ]

alertClasses :: Alert -> Array H.ClassName
alertClasses alert =
  [ H.ClassName "alert"
  , H.ClassName $ "alert--" <> levelClass alert.level
  , H.ClassName $ "alert--" <> categoryClass alert.category
  ]

levelClass :: AlertLevel -> String
levelClass = case _ of
  Info -> "info"
  Warning -> "warning"
  Critical -> "critical"
  Success -> "success"

categoryIcon :: AlertCategory -> String
categoryIcon = case _ of
  BalanceAlert -> "◉"
  RateLimitAlert -> "⚡"
  ConnectionAlert -> "🔌"
  ProofAlert -> "🔬"
  SystemAlert -> "⚠"
```

### Action Handling

```purescript
handleAction :: forall m. MonadAff m 
             => Action -> H.HalogenM State Action () Void m Unit
handleAction = case _ of
  AddAlert alert -> do
    -- Add to list
    H.modify_ \s -> s { alerts = alert : s.alerts }
    
    -- Play sound if enabled and critical
    state <- H.get
    when (state.soundEnabled && alert.level == Critical) do
      H.liftEffect playAlertSound
    
    -- Set up auto-dismiss timer
    for_ alert.autoDismissMs \ms -> do
      void $ H.fork do
        H.liftAff $ delay (Milliseconds $ toNumber ms)
        H.modify_ \s -> s { alerts = filter (\a -> a.id /= alert.id) s.alerts }
  
  DismissAlert id ->
    H.modify_ \s -> s { alerts = filter (\a -> a.id /= id) s.alerts }
  
  DismissAll ->
    H.modify_ _ { alerts = [] }
  
  ClearExpired -> do
    now <- H.liftEffect getCurrentTime
    H.modify_ \s -> s { alerts = filter (not <<< isExpired now) s.alerts }
  
  SetSoundEnabled enabled ->
    H.modify_ _ { soundEnabled = enabled }

isExpired :: DateTime -> Alert -> Boolean
isExpired now alert = case alert.autoDismissMs of
  Nothing -> false
  Just ms ->
    let expiresAt = addMilliseconds ms alert.timestamp
    in now > expiresAt
```

### Alert Helpers

```purescript
module Sidepanel.Utils.Alerts where

-- Create common alert types
lowBalanceAlert :: Number -> Number -> Alert
lowBalanceAlert diem hoursRemaining =
  { id: unsafePerformEffect generateUUID
  , category: BalanceAlert
  , level: if diem < 1.0 then Critical else Warning
  , title: "Low Diem Balance"
  , message: "Only " <> formatDiem diem <> " remaining (~" <> 
             formatHours hoursRemaining <> " at current rate)"
  , timestamp: unsafePerformEffect getCurrentTime
  , action: Just { label: "View Dashboard", onClick: navigateTo Dashboard }
  , dismissable: true
  , autoDismissMs: if diem < 1.0 then Nothing else Just 10000
  }

rateLimitAlert :: Int -> Alert
rateLimitAlert retryAfter =
  { id: unsafePerformEffect generateUUID
  , category: RateLimitAlert
  , level: Warning
  , title: "Rate Limited"
  , message: "Request limit reached. Retrying in " <> show retryAfter <> "s..."
  , timestamp: unsafePerformEffect getCurrentTime
  , action: Nothing
  , dismissable: false
  , autoDismissMs: Just (retryAfter * 1000 + 1000)
  }

connectionAlert :: Boolean -> Alert
connectionAlert isConnected =
  { id: unsafePerformEffect generateUUID
  , category: ConnectionAlert
  , level: if isConnected then Success else Critical
  , title: if isConnected then "Connected" else "Disconnected"
  , message: if isConnected 
      then "Connection to OpenCode restored"
      else "Lost connection to OpenCode. Attempting to reconnect..."
  , timestamp: unsafePerformEffect getCurrentTime
  , action: Nothing
  , dismissable: isConnected
  , autoDismissMs: if isConnected then Just 3000 else Nothing
  }

proofErrorAlert :: String -> Alert
proofErrorAlert message =
  { id: unsafePerformEffect generateUUID
  , category: ProofAlert
  , level: Warning
  , title: "Proof Error"
  , message: message
  , timestamp: unsafePerformEffect getCurrentTime
  , action: Just { label: "View Proofs", onClick: navigateTo Proofs }
  , dismissable: true
  , autoDismissMs: Just 10000
  }
```

---

## Alert Triggers

### Balance Alerts

```typescript
// bridge/src/alerts/balance.ts
class BalanceAlertTrigger {
  private lastAlertLevel: AlertLevel | null = null;
  
  check(balance: BalanceState): Alert | null {
    const { diem, metrics } = balance;
    const hoursRemaining = metrics.timeToDepletion;
    
    // Determine alert level
    let level: AlertLevel | null = null;
    
    if (diem <= 0) {
      level = 'critical';
    } else if (diem < 1 || hoursRemaining < 0.5) {
      level = 'critical';
    } else if (diem < 5 || hoursRemaining < 2) {
      level = 'warning';
    }
    
    // Only alert on level change (avoid spam)
    if (level && level !== this.lastAlertLevel) {
      this.lastAlertLevel = level;
      return this.createAlert(diem, hoursRemaining, level);
    }
    
    // Clear alert state if balance is healthy
    if (!level) {
      this.lastAlertLevel = null;
    }
    
    return null;
  }
}
```

### WebSocket Integration

```typescript
// Bridge broadcasts alerts
wsManager.on('balance.update', (balance) => {
  const alert = balanceAlertTrigger.check(balance);
  if (alert) {
    wsManager.broadcast({
      jsonrpc: '2.0',
      method: 'alert.show',
      params: alert
    });
  }
});

wsManager.on('ratelimit.hit', (info) => {
  wsManager.broadcast({
    jsonrpc: '2.0',
    method: 'alert.show',
    params: rateLimitAlert(info.retryAfter)
  });
});
```

---

## CSS Styling

```css
.alert-container {
  position: fixed;
  top: var(--space-4);
  right: var(--space-4);
  z-index: 1000;
  display: flex;
  flex-direction: column;
  gap: var(--space-2);
  max-width: 400px;
}

.alert {
  display: flex;
  align-items: flex-start;
  gap: var(--space-3);
  padding: var(--space-3);
  background: var(--color-bg-elevated);
  border: 1px solid var(--color-border-default);
  border-radius: 8px;
  box-shadow: 0 4px 12px rgba(0, 0, 0, 0.3);
  animation: slideIn 0.2s ease-out;
}

@keyframes slideIn {
  from {
    opacity: 0;
    transform: translateX(100%);
  }
  to {
    opacity: 1;
    transform: translateX(0);
  }
}

.alert--info {
  border-left: 4px solid var(--color-info);
}

.alert--warning {
  border-left: 4px solid var(--color-warning);
  background: linear-gradient(135deg, var(--color-bg-elevated) 0%, var(--color-warning-dim) 100%);
}

.alert--critical {
  border-left: 4px solid var(--color-error);
  background: linear-gradient(135deg, var(--color-bg-elevated) 0%, var(--color-error-dim) 100%);
  animation: slideIn 0.2s ease-out, pulse 2s ease-in-out infinite;
}

.alert--success {
  border-left: 4px solid var(--color-success);
}

.alert__icon {
  font-size: 20px;
  flex-shrink: 0;
}

.alert__content {
  flex: 1;
  min-width: 0;
}

.alert__title {
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  font-weight: var(--font-weight-semibold);
  color: var(--color-text-primary);
  margin-bottom: var(--space-1);
}

.alert__message {
  font-size: var(--font-size-sm);
  color: var(--color-text-secondary);
  line-height: 1.4;
}

.alert__dismiss {
  padding: var(--space-1);
  background: transparent;
  border: none;
  color: var(--color-text-tertiary);
  cursor: pointer;
  font-size: 16px;
  line-height: 1;
}

.alert__dismiss:hover {
  color: var(--color-text-primary);
}

.alert__action {
  margin-top: var(--space-2);
  padding: var(--space-1) var(--space-2);
  background: var(--color-primary-dim);
  border: 1px solid var(--color-primary);
  border-radius: 4px;
  color: var(--color-primary);
  font-family: var(--font-mono);
  font-size: var(--font-size-xs);
  cursor: pointer;
}

.alert__action:hover {
  background: var(--color-primary);
  color: white;
}

/* Mobile positioning */
@media (max-width: 768px) {
  .alert-container {
    top: auto;
    bottom: 72px; /* Above bottom nav */
    left: var(--space-2);
    right: var(--space-2);
    max-width: none;
  }
}
```

---

## Accessibility

```purescript
-- ARIA attributes for screen readers
HH.div
  [ HP.attr (H.AttrName "role") "alert"
  , HP.attr (H.AttrName "aria-live") $ case level of
      Critical -> "assertive"
      _ -> "polite"
  , HP.attr (H.AttrName "aria-atomic") "true"
  ]
```

---

## Related Specifications

- `11-DIEM-TRACKING.md` - Balance thresholds
- `14-RATE-LIMIT-HANDLING.md` - Rate limit events
- `47-THEMING.md` - Color tokens

---

*"Good alerts inform. Great alerts enable action."*
