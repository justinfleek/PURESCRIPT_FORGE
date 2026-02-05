# 35-CONNECTION-STATUS: WebSocket Connection Management

## Overview

The Connection Status system monitors the WebSocket connection to the bridge server, provides visual feedback, handles reconnection, and notifies users of connectivity issues.

---

## Connection States

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         CONNECTION STATE MACHINE                            │
│                                                                              │
│  ┌──────────────┐                                                           │
│  │ DISCONNECTED │ ──── connect() ────► ┌────────────┐                      │
│  └──────────────┘                       │ CONNECTING │                      │
│         ▲                               └────────────┘                      │
│         │                                     │                              │
│    close/error                          onopen()                            │
│         │                                     │                              │
│         │         ◄─── onclose() ────   ┌────▼───────┐                      │
│         └───────────────────────────────│ CONNECTED  │                      │
│                                         └────────────┘                      │
│                                               │                              │
│                                          onclose()                          │
│                                               │                              │
│                                         ┌────▼───────┐                      │
│                                         │RECONNECTING│ ─── max retries ──► │
│                                         └────────────┘        DISCONNECTED  │
│                                               │                              │
│                                           onopen()                          │
│                                               │                              │
│                                         ┌────▼───────┐                      │
│                                         │ CONNECTED  │                      │
│                                         └────────────┘                      │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Visual Design

### Status Indicator (Normal - Connected)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  ● Connected                                                                │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Status Indicator (Connecting)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  ◐ Connecting...                                                            │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Status Indicator (Reconnecting)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  ◐ Reconnecting... (attempt 2/5)                                           │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Status Indicator (Disconnected)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  ○ Disconnected                                                [Reconnect] │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Connection Banner (On Disconnect)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  ⚠ Connection lost. Attempting to reconnect...              [Retry Now] [✕]│
└─────────────────────────────────────────────────────────────────────────────┘
```

### Connection Details Popover

```
┌────────────────────────────────────────────────┐
│  CONNECTION DETAILS                            │
├────────────────────────────────────────────────┤
│                                                │
│  Status: ● Connected                           │
│  Server: ws://localhost:3000/ws                │
│  Latency: 12ms                                 │
│  Uptime: 2h 34m                                │
│                                                │
│  Last message: 3s ago                          │
│  Messages sent: 1,234                          │
│  Messages received: 5,678                      │
│                                                │
│  [Disconnect]  [View Logs]                     │
└────────────────────────────────────────────────┘
```

---

## Data Model

```typescript
interface ConnectionState {
  status: ConnectionStatus;
  
  // Connection info
  url: string;
  connectedAt?: Date;
  
  // Reconnection
  reconnectAttempts: number;
  maxReconnectAttempts: number;
  nextReconnectIn?: number;  // ms
  
  // Metrics
  latency: number;  // ms
  messagesSent: number;
  messagesReceived: number;
  lastMessageAt?: Date;
  
  // Errors
  lastError?: ConnectionError;
}

type ConnectionStatus =
  | 'disconnected'
  | 'connecting'
  | 'connected'
  | 'reconnecting'
  | 'failed';

interface ConnectionError {
  code: number;
  reason: string;
  timestamp: Date;
  recoverable: boolean;
}

interface ReconnectConfig {
  maxAttempts: number;
  initialDelay: number;      // ms
  maxDelay: number;          // ms
  backoffMultiplier: number;
}
```

---

## Reconnection Strategy

### Exponential Backoff

```typescript
// bridge/src/websocket/reconnect.ts

const DEFAULT_CONFIG: ReconnectConfig = {
  maxAttempts: 5,
  initialDelay: 1000,      // 1 second
  maxDelay: 30000,         // 30 seconds
  backoffMultiplier: 2.0
};

export class ReconnectionManager {
  private config: ReconnectConfig;
  private attempts: number = 0;
  private timer: NodeJS.Timer | null = null;
  
  constructor(config: Partial<ReconnectConfig> = {}) {
    this.config = { ...DEFAULT_CONFIG, ...config };
  }
  
  scheduleReconnect(connect: () => void): void {
    if (this.attempts >= this.config.maxAttempts) {
      this.onMaxAttemptsReached();
      return;
    }
    
    const delay = this.calculateDelay();
    this.attempts++;
    
    // Notify UI
    this.broadcast({
      status: 'reconnecting',
      attempt: this.attempts,
      maxAttempts: this.config.maxAttempts,
      nextReconnectIn: delay
    });
    
    this.timer = setTimeout(() => {
      connect();
    }, delay);
  }
  
  private calculateDelay(): number {
    // Exponential backoff with jitter
    const exponentialDelay = this.config.initialDelay * 
      Math.pow(this.config.backoffMultiplier, this.attempts);
    
    const cappedDelay = Math.min(exponentialDelay, this.config.maxDelay);
    
    // Add ±20% jitter to prevent thundering herd
    const jitter = cappedDelay * 0.2 * (Math.random() * 2 - 1);
    
    return Math.round(cappedDelay + jitter);
  }
  
  onConnected(): void {
    this.attempts = 0;
    this.clearTimer();
  }
  
  onDisconnected(): void {
    // Will be called by WebSocket onclose handler
  }
  
  reset(): void {
    this.attempts = 0;
    this.clearTimer();
  }
  
  private clearTimer(): void {
    if (this.timer) {
      clearTimeout(this.timer);
      this.timer = null;
    }
  }
  
  private onMaxAttemptsReached(): void {
    this.broadcast({
      status: 'failed',
      error: {
        code: 1006,
        reason: 'Max reconnection attempts reached',
        recoverable: true
      }
    });
  }
}
```

---

## PureScript Implementation

### Types

```purescript
module Sidepanel.Connection where

import Prelude
import Data.Maybe (Maybe)
import Data.DateTime (DateTime)

data ConnectionStatus
  = Disconnected
  | Connecting
  | Connected
  | Reconnecting
  | Failed

type ConnectionState =
  { status :: ConnectionStatus
  , url :: String
  , connectedAt :: Maybe DateTime
  , reconnectAttempts :: Int
  , maxReconnectAttempts :: Int
  , nextReconnectIn :: Maybe Int
  , latency :: Int
  , lastMessageAt :: Maybe DateTime
  , lastError :: Maybe ConnectionError
  }

type ConnectionError =
  { code :: Int
  , reason :: String
  , recoverable :: Boolean
  }

data Action
  = Connect
  | Disconnect
  | StatusChanged ConnectionStatus
  | ErrorOccurred ConnectionError
  | ReconnectScheduled Int Int  -- attempt, delay
  | LatencyMeasured Int
  | MessageReceived
  | RetryNow
  | DismissBanner
```

### Status Indicator Component

```purescript
module Sidepanel.Components.ConnectionStatus where

component :: forall q m. MonadAff m => H.Component q ConnectionState Output m
component = H.mkComponent
  { initialState: identity
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      }
  }

render :: forall m. ConnectionState -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "connection-status") ]
    [ renderIndicator state
    , when (shouldShowBanner state) $ renderBanner state
    ]

renderIndicator :: forall m. ConnectionState -> H.ComponentHTML Action () m
renderIndicator state =
  HH.div
    [ HP.classes $ indicatorClasses state.status
    , HP.title $ statusTooltip state
    , HE.onClick \_ -> ToggleDetails
    ]
    [ HH.span [ HP.class_ (H.ClassName "status-dot") ]
        [ HH.text $ statusDot state.status ]
    , HH.span [ HP.class_ (H.ClassName "status-text") ]
        [ HH.text $ statusText state ]
    ]

statusDot :: ConnectionStatus -> String
statusDot = case _ of
  Disconnected -> "○"
  Connecting -> "◐"
  Connected -> "●"
  Reconnecting -> "◐"
  Failed -> "○"

statusText :: ConnectionState -> String
statusText state = case state.status of
  Disconnected -> "Disconnected"
  Connecting -> "Connecting..."
  Connected -> "Connected"
  Reconnecting -> "Reconnecting... (" <> show state.reconnectAttempts <> "/" <> 
                  show state.maxReconnectAttempts <> ")"
  Failed -> "Connection Failed"

renderBanner :: forall m. ConnectionState -> H.ComponentHTML Action () m
renderBanner state =
  HH.div
    [ HP.class_ (H.ClassName "connection-banner") ]
    [ HH.span [ HP.class_ (H.ClassName "banner-icon") ] [ HH.text "⚠" ]
    , HH.span [ HP.class_ (H.ClassName "banner-message") ]
        [ HH.text $ bannerMessage state ]
    , HH.button
        [ HP.class_ (H.ClassName "banner-action")
        , HE.onClick \_ -> RetryNow
        ]
        [ HH.text "Retry Now" ]
    , HH.button
        [ HP.class_ (H.ClassName "banner-dismiss")
        , HE.onClick \_ -> DismissBanner
        ]
        [ HH.text "✕" ]
    ]

bannerMessage :: ConnectionState -> String
bannerMessage state = case state.status of
  Reconnecting -> "Connection lost. Reconnecting in " <> 
                  formatDuration (fromMaybe 0 state.nextReconnectIn) <> "..."
  Failed -> "Unable to connect after " <> show state.reconnectAttempts <> " attempts."
  Disconnected -> "You are offline. Some features may be unavailable."
  _ -> ""

shouldShowBanner :: ConnectionState -> Boolean
shouldShowBanner state = case state.status of
  Reconnecting -> true
  Failed -> true
  Disconnected -> true
  _ -> false
```

---

## CSS Styling

```css
.connection-status {
  display: flex;
  align-items: center;
  gap: var(--space-2);
}

.status-indicator {
  display: flex;
  align-items: center;
  gap: var(--space-1);
  padding: var(--space-1) var(--space-2);
  border-radius: 4px;
  font-size: var(--font-size-xs);
  cursor: pointer;
  transition: background var(--transition-fast);
}

.status-indicator:hover {
  background: var(--color-bg-hover);
}

.status-dot {
  font-size: 10px;
}

.status-indicator--connected .status-dot {
  color: var(--color-success);
}

.status-indicator--connecting .status-dot,
.status-indicator--reconnecting .status-dot {
  color: var(--color-warning);
  animation: pulse 1s ease-in-out infinite;
}

.status-indicator--disconnected .status-dot,
.status-indicator--failed .status-dot {
  color: var(--color-error);
}

@keyframes pulse {
  0%, 100% { opacity: 1; }
  50% { opacity: 0.4; }
}

.status-text {
  color: var(--color-text-secondary);
}

/* Connection banner */
.connection-banner {
  position: fixed;
  top: 0;
  left: 0;
  right: 0;
  display: flex;
  align-items: center;
  gap: var(--space-3);
  padding: var(--space-2) var(--space-4);
  background: var(--color-warning-dim);
  border-bottom: 1px solid var(--color-warning);
  z-index: 100;
  animation: slideDown 0.2s ease-out;
}

.connection-banner--error {
  background: var(--color-error-dim);
  border-color: var(--color-error);
}

.banner-icon {
  font-size: 16px;
  color: var(--color-warning);
}

.banner-message {
  flex: 1;
  font-size: var(--font-size-sm);
  color: var(--color-text-primary);
}

.banner-action {
  padding: var(--space-1) var(--space-2);
  background: var(--color-warning);
  color: white;
  border: none;
  border-radius: 4px;
  font-size: var(--font-size-xs);
  cursor: pointer;
}

.banner-dismiss {
  background: none;
  border: none;
  color: var(--color-text-secondary);
  cursor: pointer;
  padding: var(--space-1);
}

/* Details popover */
.connection-details {
  position: absolute;
  top: 100%;
  right: 0;
  margin-top: var(--space-2);
  min-width: 280px;
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-default);
  border-radius: 8px;
  box-shadow: var(--shadow-lg);
  z-index: 50;
}

.connection-details__header {
  padding: var(--space-3);
  font-weight: var(--font-weight-semibold);
  border-bottom: 1px solid var(--color-border-subtle);
}

.connection-details__content {
  padding: var(--space-3);
}

.connection-details__row {
  display: flex;
  justify-content: space-between;
  margin-bottom: var(--space-2);
  font-size: var(--font-size-sm);
}

.connection-details__label {
  color: var(--color-text-secondary);
}

.connection-details__value {
  color: var(--color-text-primary);
  font-family: var(--font-mono);
}
```

---

## Latency Measurement

```typescript
// Ping/pong latency measurement
class LatencyMonitor {
  private lastPingTime: number = 0;
  private latencies: number[] = [];
  private maxSamples: number = 10;
  
  sendPing(ws: WebSocket): void {
    this.lastPingTime = Date.now();
    ws.send(JSON.stringify({ jsonrpc: '2.0', method: 'ping', id: 'ping' }));
  }
  
  receivePong(): void {
    const latency = Date.now() - this.lastPingTime;
    this.latencies.push(latency);
    
    if (this.latencies.length > this.maxSamples) {
      this.latencies.shift();
    }
    
    this.broadcast({ latency: this.getAverageLatency() });
  }
  
  getAverageLatency(): number {
    if (this.latencies.length === 0) return 0;
    return Math.round(
      this.latencies.reduce((a, b) => a + b, 0) / this.latencies.length
    );
  }
}
```

---

## Related Specifications

- `31-WEBSOCKET-PROTOCOL.md` - WebSocket protocol
- `32-STATE-SYNCHRONIZATION.md` - State sync
- `56-ALERT-SYSTEM.md` - Alert notifications

---

*"Always know your connection status. Never lose your work."*
