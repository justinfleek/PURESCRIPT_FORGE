# 82-DEBUG-MODE: Developer Tools and Diagnostics

## Overview

Debug Mode provides developer tools for troubleshooting, inspecting state, testing features, and diagnosing issues. Hidden by default, activated via settings or keyboard shortcut.

---

## Activation

- **Keyboard**: `Ctrl+Shift+D` (toggle)
- **Settings**: Settings → Advanced → Enable Debug Mode
- **URL**: Add `?debug=true` to URL
- **Console**: `window.__SIDEPANEL_DEBUG__ = true`

---

## Visual Design

### Debug Panel

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  🔧 DEBUG MODE                                          [Pause] [Clear] [✕] │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ TABS ────────────────────────────────────────────────────────────────┐ │
│  │  [State]  [Events]  [Network]  [Performance]  [Console]  [Tools]      │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ STATE INSPECTOR ─────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ▼ balance                                                            │ │
│  │    ├─ diem: 42.5                                                      │ │
│  │    ├─ usd: 0.42                                                       │ │
│  │    ├─ burnRate: 5.2                                                   │ │
│  │    └─ alertLevel: "normal"                                            │ │
│  │                                                                        │ │
│  │  ▼ session                                                            │ │
│  │    ├─ id: "sess_abc123"                                               │ │
│  │    ├─ title: "Debug Auth"                                             │ │
│  │    ├─ messageCount: 12                                                │ │
│  │    └─ ▼ messages [12]                                                 │ │
│  │        ├─ [0] { role: "user", ... }                                   │ │
│  │        ├─ [1] { role: "assistant", ... }                              │ │
│  │        └─ ...                                                         │ │
│  │                                                                        │ │
│  │  ▶ connection                                                         │ │
│  │  ▶ settings                                                           │ │
│  │  ▶ ui                                                                 │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Event Log Tab

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  🔧 DEBUG MODE                                          [Pause] [Clear] [✕] │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ TABS ────────────────────────────────────────────────────────────────┐ │
│  │  [State]  [Events]  [Network]  [Performance]  [Console]  [Tools]      │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  Filter: [All ▼] [🔍 Search...]                                            │
│                                                                             │
│  ┌─ EVENT LOG ───────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  14:32:05.123  ws.message        balance.update      { diem: 42.5 }   │ │
│  │  14:32:04.891  action           Navigate            Dashboard         │ │
│  │  14:32:04.567  ws.message        session.update      { id: "sess..." }│ │
│  │  14:32:03.234  ws.send           ping                                 │ │
│  │  14:32:02.112  action           SetQuery            "session"         │ │
│  │  14:32:01.890  render           CommandPalette      12ms              │ │
│  │  14:32:01.456  action           OpenCommandPalette                    │ │
│  │  14:32:00.123  ws.open                                                │ │
│  │  14:31:59.890  ws.connecting    ws://localhost:3000                   │ │
│  │                                                                        │ │
│  │  [Load More...]                                                       │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Network Tab

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  🔧 DEBUG MODE                                          [Pause] [Clear] [✕] │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ NETWORK ─────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  WebSocket: ws://localhost:3000/ws                                    │ │
│  │  Status: ● Connected (2h 34m)                                         │ │
│  │  Latency: 12ms avg                                                    │ │
│  │                                                                        │ │
│  │  ┌─ MESSAGES ─────────────────────────────────────────────────────┐  │ │
│  │  │                                                                 │  │ │
│  │  │  14:32:05 ← balance.update     234 bytes    12ms               │  │ │
│  │  │  14:32:04 → session.get        89 bytes     -                  │  │ │
│  │  │  14:32:03 ← pong               32 bytes     8ms                │  │ │
│  │  │  14:32:03 → ping               32 bytes     -                  │  │ │
│  │  │  14:32:02 ← session.update     1.2 KB       45ms               │  │ │
│  │  │                                                                 │  │ │
│  │  └─────────────────────────────────────────────────────────────────┘  │ │
│  │                                                                        │ │
│  │  Total: 1,234 messages | 456 KB sent | 2.3 MB received               │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Tools Tab

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  🔧 DEBUG MODE                                                         [✕] │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ QUICK ACTIONS ───────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  [Force Reconnect]  [Clear Storage]  [Reset State]  [Export Logs]    │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ SIMULATE ────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  Balance Warning:   [Low (10)]  [Critical (5)]  [Empty (0)]          │ │
│  │  Connection:        [Disconnect]  [Reconnecting]  [Failed]           │ │
│  │  Notification:      [Success]  [Warning]  [Error]                    │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ INJECT STATE ────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ┌─────────────────────────────────────────────────────────────────┐ │ │
│  │  │ {                                                                │ │ │
│  │  │   "balance": { "diem": 5.0 },                                   │ │ │
│  │  │   "session": { "id": "test" }                                   │ │ │
│  │  │ }                                                                │ │ │
│  │  └─────────────────────────────────────────────────────────────────┘ │ │
│  │                                                          [Apply]      │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Data Model

```typescript
interface DebugState {
  enabled: boolean;
  activeTab: DebugTab;
  isPaused: boolean;
  
  // Event log
  events: DebugEvent[];
  eventFilter: string;
  maxEvents: number;
  
  // Network
  networkMessages: NetworkMessage[];
  
  // Performance
  renderTimes: Map<string, number[]>;
  
  // Console
  consoleOutput: ConsoleEntry[];
}

type DebugTab = 
  | 'state'
  | 'events'
  | 'network'
  | 'performance'
  | 'console'
  | 'tools';

interface DebugEvent {
  id: string;
  timestamp: Date;
  type: EventType;
  category: string;
  payload: any;
  duration?: number;
}

type EventType =
  | 'action'
  | 'ws.send'
  | 'ws.message'
  | 'ws.open'
  | 'ws.close'
  | 'ws.error'
  | 'render'
  | 'effect'
  | 'error';

interface NetworkMessage {
  id: string;
  timestamp: Date;
  direction: 'in' | 'out';
  method: string;
  payload: any;
  size: number;
  duration?: number;
}

interface ConsoleEntry {
  id: string;
  timestamp: Date;
  level: 'log' | 'info' | 'warn' | 'error';
  message: string;
  data?: any;
}
```

---

## Debug Service

```typescript
// bridge/src/debug/service.ts

class DebugService {
  private enabled: boolean = false;
  private events: DebugEvent[] = [];
  private maxEvents: number = 1000;
  
  enable(): void {
    this.enabled = true;
    this.interceptWebSocket();
    this.interceptConsole();
    console.log('[Debug] Debug mode enabled');
  }
  
  disable(): void {
    this.enabled = false;
    this.restoreWebSocket();
    this.restoreConsole();
  }
  
  log(event: Omit<DebugEvent, 'id' | 'timestamp'>): void {
    if (!this.enabled) return;
    
    this.events.push({
      id: generateId(),
      timestamp: new Date(),
      ...event
    });
    
    // Trim old events
    if (this.events.length > this.maxEvents) {
      this.events = this.events.slice(-this.maxEvents);
    }
    
    // Broadcast to debug panel
    this.broadcast({ type: 'debug.event', event });
  }
  
  logAction(category: string, payload: any): void {
    this.log({ type: 'action', category, payload });
  }
  
  logRender(component: string, duration: number): void {
    this.log({ type: 'render', category: component, payload: null, duration });
  }
  
  private interceptWebSocket(): void {
    const originalSend = WebSocket.prototype.send;
    const self = this;
    
    WebSocket.prototype.send = function(data: string) {
      self.log({
        type: 'ws.send',
        category: 'websocket',
        payload: JSON.parse(data)
      });
      return originalSend.call(this, data);
    };
  }
  
  // Simulation helpers
  simulateLowBalance(): void {
    this.broadcast({
      type: 'balance.update',
      payload: { diem: 5.0, usd: 0.05, alertLevel: 'warning' }
    });
  }
  
  simulateDisconnect(): void {
    this.broadcast({
      type: 'connection.status',
      payload: { status: 'disconnected' }
    });
  }
  
  exportLogs(): string {
    return JSON.stringify({
      exportedAt: new Date().toISOString(),
      events: this.events,
      state: this.getState()
    }, null, 2);
  }
}

export const debug = new DebugService();
```

---

## PureScript Integration

```purescript
module Sidepanel.Debug where

import Prelude
import Effect (Effect)

-- Debug logging
foreign import debugLog :: String -> Effect Unit
foreign import debugLogAction :: String -> Foreign -> Effect Unit
foreign import debugLogRender :: String -> Number -> Effect Unit

-- Conditional debug wrapper
whenDebug :: forall m. MonadEffect m => m Unit -> m Unit
whenDebug action = do
  enabled <- liftEffect isDebugEnabled
  when enabled action

-- Performance timing
timeAction :: forall m a. MonadAff m => String -> m a -> m a
timeAction label action = do
  start <- liftEffect now
  result <- action
  end <- liftEffect now
  liftEffect $ debugLogRender label (end - start)
  pure result

-- Usage in components
handleAction = case _ of
  SomeAction payload -> do
    liftEffect $ debugLogAction "SomeAction" (toForeign payload)
    -- ... actual handling
```

---

## Console Commands

```javascript
// Available in browser console when debug mode is enabled

window.sidepanel = {
  // State inspection
  getState: () => store.getState(),
  getBalance: () => store.getState().balance,
  getSession: () => store.getState().session,
  
  // Actions
  navigate: (route) => router.navigate(route),
  setBalance: (diem) => store.dispatch({ type: 'SET_BALANCE', diem }),
  
  // Simulation
  simulateLowBalance: () => debug.simulateLowBalance(),
  simulateDisconnect: () => debug.simulateDisconnect(),
  simulateError: (msg) => debug.simulateError(msg),
  
  // Export
  exportState: () => JSON.stringify(store.getState(), null, 2),
  exportLogs: () => debug.exportLogs(),
  
  // Performance
  measureRender: (component) => debug.measureRender(component),
  
  // Version info
  version: () => ({ version: '0.1.0', build: 'dev' })
};

console.log('Sidepanel debug tools available. Type `sidepanel` for commands.');
```

---

## CSS Styling

```css
.debug-panel {
  position: fixed;
  bottom: 0;
  left: 0;
  right: 0;
  height: 300px;
  background: #1a1a2e;
  border-top: 2px solid #8b5cf6;
  z-index: 9999;
  display: flex;
  flex-direction: column;
  font-family: 'JetBrains Mono', monospace;
  font-size: 12px;
}

.debug-panel__header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: 8px 16px;
  background: #0f0f1a;
  border-bottom: 1px solid #2a2a4a;
}

.debug-panel__title {
  display: flex;
  align-items: center;
  gap: 8px;
  color: #8b5cf6;
  font-weight: 600;
}

.debug-tabs {
  display: flex;
  gap: 4px;
  padding: 8px;
  background: #0f0f1a;
}

.debug-tab {
  padding: 4px 12px;
  background: transparent;
  border: none;
  border-radius: 4px;
  color: #a1a1aa;
  cursor: pointer;
}

.debug-tab:hover {
  background: #2a2a4a;
}

.debug-tab--active {
  background: #8b5cf6;
  color: white;
}

.debug-content {
  flex: 1;
  overflow: auto;
  padding: 8px;
}

.debug-event {
  display: flex;
  gap: 12px;
  padding: 4px 8px;
  border-bottom: 1px solid #2a2a4a;
}

.debug-event__time {
  color: #71717a;
  min-width: 100px;
}

.debug-event__type {
  min-width: 100px;
  color: #22c55e;
}

.debug-event__category {
  min-width: 120px;
  color: #f59e0b;
}

.debug-event__payload {
  color: #e4e4e7;
  flex: 1;
  overflow: hidden;
  text-overflow: ellipsis;
  white-space: nowrap;
}
```

---

## Related Specifications

- `80-ERROR-TAXONOMY.md` - Error handling
- `67-PERFORMANCE-PROFILER.md` - Performance metrics
- `72-INTEGRATION-TESTING.md` - Testing tools

---

*"Debug mode: see everything, control everything, break nothing."*
