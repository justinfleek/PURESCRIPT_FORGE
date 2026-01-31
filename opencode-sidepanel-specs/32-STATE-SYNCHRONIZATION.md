# 32-STATE-SYNCHRONIZATION: Bridge-Browser State Sync

## Overview

State synchronization ensures the browser UI accurately reflects the bridge server's state. This document covers the sync protocol, conflict resolution, and optimistic updates.

---

## State Ownership

### Single Source of Truth

The **bridge server** owns all authoritative state:

| State | Owner | Reason |
|-------|-------|--------|
| Balance | Bridge | Extracted from Venice API headers |
| Session | Bridge | From OpenCode plugin events |
| Proof State | Bridge | From Lean LSP proxy |
| Usage Metrics | Bridge | Aggregated from multiple sources |
| Snapshots | Bridge | Stored in SQLite |

The browser maintains a **local copy** for rendering, updated via WebSocket.

### Why Bridge-Owned?

1. **Security** - API keys never reach browser
2. **Reliability** - Bridge survives browser refresh
3. **Aggregation** - Bridge combines multiple data sources
4. **Persistence** - Bridge has database access

---

## Sync Protocol

### Initial Sync

When browser connects, it receives full state:

```
Browser                    Bridge
   │                         │
   │──── Connect ───────────►│
   │                         │
   │◄──── Auth Challenge ────│
   │                         │
   │──── Auth Token ────────►│
   │                         │
   │◄──── Full State ────────│  (initial snapshot)
   │                         │
   │◄──── Subscribed ────────│  (confirm ready)
   │                         │
```

### Full State Message

```typescript
interface FullStateMessage {
  jsonrpc: "2.0";
  method: "state.sync";
  params: {
    connected: boolean;
    balance: BalanceState;
    session: SessionState | null;
    proof: ProofState;
    metrics: UsageMetrics;
    snapshots: SnapshotSummary[];
    timestamp: string;  // ISO 8601
  };
}
```

### Incremental Updates

After initial sync, only changes are sent:

```typescript
// Balance update
{
  jsonrpc: "2.0",
  method: "balance.update",
  params: {
    diem: 42.5,
    usd: 10.0,
    effective: 52.5,
    lastUpdated: "2024-01-15T10:30:00Z"
  }
}

// Session update
{
  jsonrpc: "2.0",
  method: "session.update",
  params: {
    id: "sess_abc123",
    promptTokens: 15234,
    completionTokens: 8721,
    cost: 0.014
  }
}

// Partial update (only changed fields)
{
  jsonrpc: "2.0",
  method: "session.update",
  params: {
    promptTokens: 15500  // Only this changed
  }
}
```

---

## Bridge Implementation

### State Store with Broadcasting

```typescript
// bridge/src/state/store.ts
import { EventEmitter } from 'events';

export class StateStore extends EventEmitter {
  private state: AppState;
  private wsManager: WebSocketManager;
  
  constructor(wsManager: WebSocketManager) {
    super();
    this.state = initialState();
    this.wsManager = wsManager;
    
    // When state changes, broadcast to all clients
    this.on('change', (path: string, value: any) => {
      this.broadcastUpdate(path, value);
    });
  }
  
  // Get current state (immutable copy)
  getState(): AppState {
    return structuredClone(this.state);
  }
  
  // Update balance (called by Venice proxy)
  updateBalance(partial: Partial<BalanceState>): void {
    const prev = this.state.balance;
    this.state.balance = { ...prev, ...partial, lastUpdated: new Date() };
    
    // Only broadcast changed fields
    const changes = this.diff(prev, this.state.balance);
    if (Object.keys(changes).length > 0) {
      this.emit('change', 'balance', changes);
    }
  }
  
  // Update session (called by OpenCode client)
  updateSession(partial: Partial<SessionState>): void {
    if (!this.state.session && partial.id) {
      // New session
      this.state.session = partial as SessionState;
      this.emit('change', 'session', this.state.session);
    } else if (this.state.session) {
      const prev = this.state.session;
      this.state.session = { ...prev, ...partial };
      
      const changes = this.diff(prev, this.state.session);
      if (Object.keys(changes).length > 0) {
        this.emit('change', 'session', changes);
      }
    }
  }
  
  // Broadcast to all connected clients
  private broadcastUpdate(path: string, value: any): void {
    this.wsManager.broadcast({
      jsonrpc: '2.0',
      method: `${path}.update`,
      params: value
    });
  }
  
  // Calculate diff between objects
  private diff(prev: any, next: any): Record<string, any> {
    const changes: Record<string, any> = {};
    for (const key of Object.keys(next)) {
      if (prev[key] !== next[key]) {
        changes[key] = next[key];
      }
    }
    return changes;
  }
}
```

### Initial State Sync Handler

```typescript
// bridge/src/websocket/handlers.ts

export async function handleStateGet(
  store: StateStore,
  client: ClientConnection,
  request: JsonRpcRequest
): Promise<JsonRpcResponse> {
  const state = store.getState();
  
  return {
    jsonrpc: '2.0',
    id: request.id,
    result: {
      connected: state.connected,
      balance: state.balance,
      session: state.session,
      proof: state.proof,
      metrics: state.metrics,
      snapshots: state.snapshots.map(s => ({
        id: s.id,
        timestamp: s.timestamp,
        description: s.description
      })),
      timestamp: new Date().toISOString()
    }
  };
}
```

---

## Browser Implementation

### State Reducer

```purescript
module Sidepanel.State.Reducer where

import Prelude
import Data.Maybe (Maybe(..))

-- All possible state updates
data StateAction
  = FullSync AppState
  | UpdateBalance BalanceUpdate
  | UpdateSession SessionUpdate
  | UpdateProof ProofUpdate
  | UpdateMetrics MetricsUpdate
  | SetConnected Boolean
  | ClearSession

-- Pure reducer function
reduce :: AppState -> StateAction -> AppState
reduce state action = case action of
  FullSync newState -> 
    newState
  
  UpdateBalance update ->
    state { balance = mergeBalance state.balance update }
  
  UpdateSession update ->
    state { session = Just $ mergeSession state.session update }
  
  UpdateProof update ->
    state { proof = mergeProof state.proof update }
  
  UpdateMetrics update ->
    state { metrics = mergeMetrics state.metrics update }
  
  SetConnected connected ->
    state { connected = connected }
  
  ClearSession ->
    state { session = Nothing }

-- Merge helpers (handle partial updates)
mergeBalance :: BalanceState -> BalanceUpdate -> BalanceState
mergeBalance current update =
  { diem: fromMaybe current.diem update.diem
  , usd: fromMaybe current.usd update.usd
  , effective: fromMaybe current.effective update.effective
  , lastUpdated: fromMaybe current.lastUpdated update.lastUpdated
  , history: current.history  -- History updated separately
  , metrics: fromMaybe current.metrics update.metrics
  , alertLevel: fromMaybe current.alertLevel update.alertLevel
  }
```

### WebSocket Message Handler

```purescript
module Sidepanel.Api.WebSocket where

import Prelude
import Data.Argonaut (decodeJson, class DecodeJson)
import Effect.Aff (Aff)

-- Handle incoming WebSocket message
handleMessage :: Store AppState -> ServerMessage -> Aff Unit
handleMessage store msg = do
  let action = messageToAction msg
  for_ action \a -> do
    liftEffect $ Store.dispatch store a

-- Convert WebSocket message to state action
messageToAction :: ServerMessage -> Maybe StateAction
messageToAction msg = case msg.method of
  "state.sync" -> 
    FullSync <$> decodeJson msg.params
  
  "balance.update" ->
    UpdateBalance <$> decodeJson msg.params
  
  "session.update" ->
    UpdateSession <$> decodeJson msg.params
  
  "session.cleared" ->
    Just ClearSession
  
  "proof.update" ->
    UpdateProof <$> decodeJson msg.params
  
  "usage.update" ->
    UpdateMetrics <$> decodeJson msg.params
  
  _ -> Nothing  -- Unknown message type
```

---

## Reconnection Sync

When browser reconnects after disconnect:

```
Browser                    Bridge
   │                         │
   │  (disconnected)         │
   │                         │
   │──── Reconnect ─────────►│
   │                         │
   │◄──── Auth Challenge ────│
   │                         │
   │──── Auth + lastSync ───►│  (send last known timestamp)
   │                         │
   │◄──── Delta Updates ─────│  (only changes since lastSync)
   │     OR                   │
   │◄──── Full State ────────│  (if too many changes)
   │                         │
```

### Delta Sync Request

```typescript
// Browser sends its last sync timestamp
{
  jsonrpc: "2.0",
  id: 1,
  method: "state.get",
  params: {
    since: "2024-01-15T10:25:00Z"  // Last sync time
  }
}

// Bridge responds with changes since that time
{
  jsonrpc: "2.0",
  id: 1,
  result: {
    type: "delta",  // Or "full" if too many changes
    changes: [
      { path: "balance", value: { diem: 40.0, usd: 10.0 } },
      { path: "session.promptTokens", value: 15500 }
    ],
    timestamp: "2024-01-15T10:30:00Z"
  }
}
```

---

## Conflict Resolution

### Last-Write-Wins

For most state, we use simple last-write-wins:

```typescript
// Bridge always wins - it's the source of truth
// Browser optimistic updates are overwritten
```

### Optimistic Updates (User Actions)

For user-initiated actions (like changing settings), we use optimistic updates:

```purescript
-- User changes alert threshold
handleSetThreshold :: Number -> H.HalogenM State Action () Output m Unit
handleSetThreshold threshold = do
  -- 1. Optimistically update local state
  H.modify_ \s -> s { alertThreshold = threshold }
  
  -- 2. Send to bridge
  result <- sendMessage 
    { method: "alerts.configure"
    , params: { warningPercent: threshold }
    }
  
  -- 3. If failed, rollback
  case result of
    Left error -> do
      -- Restore previous value
      H.modify_ \s -> s { alertThreshold = previousThreshold }
      -- Show error to user
      showError error
    Right _ ->
      pure unit  -- Server confirmed, we're good
```

---

## Heartbeat and Staleness

### Heartbeat Protocol

```
Browser                    Bridge
   │                         │
   │◄──── ping ──────────────│  (every 30s)
   │                         │
   │──── pong ──────────────►│
   │                         │
```

### Staleness Detection

```purescript
-- If no messages for 60s, consider connection stale
checkStaleness :: State -> Effect Unit
checkStaleness state = do
  now <- getCurrentTime
  let sinceLastMessage = diffSeconds now state.lastMessageTime
  
  when (sinceLastMessage > 60) do
    -- Mark as potentially disconnected
    dispatch SetConnected false
    -- Attempt reconnect
    reconnect
```

---

## Testing

### Sync Test Cases

```typescript
describe('State Synchronization', () => {
  it('performs full sync on connect', async () => {
    const { bridge, browser } = await setupTestEnvironment();
    
    // Set some state on bridge
    bridge.store.updateBalance({ diem: 42.5, usd: 10.0 });
    
    // Connect browser
    await browser.connect();
    
    // Browser should have synced state
    expect(browser.state.balance.diem).toBe(42.5);
  });
  
  it('receives incremental updates', async () => {
    const { bridge, browser } = await setupTestEnvironment();
    await browser.connect();
    
    // Update balance on bridge
    bridge.store.updateBalance({ diem: 40.0 });
    
    // Wait for broadcast
    await waitForMessage(browser);
    
    // Browser should be updated
    expect(browser.state.balance.diem).toBe(40.0);
  });
  
  it('handles reconnection with delta sync', async () => {
    const { bridge, browser } = await setupTestEnvironment();
    await browser.connect();
    
    // Disconnect
    browser.disconnect();
    
    // Bridge state changes while disconnected
    bridge.store.updateBalance({ diem: 35.0 });
    bridge.store.updateSession({ promptTokens: 5000 });
    
    // Reconnect
    await browser.connect();
    
    // Browser should have latest state
    expect(browser.state.balance.diem).toBe(35.0);
    expect(browser.state.session.promptTokens).toBe(5000);
  });
});
```

---

## Related Specifications

- `30-BRIDGE-ARCHITECTURE.md` - Bridge server design
- `31-WEBSOCKET-PROTOCOL.md` - WebSocket messages
- `40-PURESCRIPT-ARCHITECTURE.md` - Frontend state

---

*"Sync is easy when there's one source of truth."*
