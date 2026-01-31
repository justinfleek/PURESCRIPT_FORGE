# 31-WEBSOCKET-PROTOCOL: Bridge-Browser Communication Protocol

## Overview

The WebSocket connection between the Bridge Server and Browser Client uses JSON-RPC 2.0 as the message format. This provides structured request/response patterns with proper error handling.

**Connection URL:** `ws://localhost:8765/ws`
**Protocol:** JSON-RPC 2.0 over WebSocket

---

## Connection Lifecycle

### Connection Flow

```
Browser                          Bridge Server
   │                                   │
   │ ──── WebSocket Connect ─────────► │
   │                                   │
   │ ◄──── Connection Accepted ─────── │
   │                                   │
   │ ──── auth.request ──────────────► │
   │                                   │
   │ ◄──── auth.response ───────────── │
   │                                   │
   │ ──── state.subscribe ───────────► │
   │                                   │
   │ ◄──── state.full ─────────────── │
   │                                   │
   │ ◄──── state.update ───────────── │ (ongoing)
   │ ◄──── state.update ───────────── │
   │       ...                         │
   │                                   │
```

### Connection Establishment

```typescript
// Browser side
const ws = new WebSocket('ws://localhost:8765/ws');

ws.onopen = () => {
  // Authenticate (if required)
  ws.send(JSON.stringify({
    jsonrpc: '2.0',
    id: 1,
    method: 'auth.request',
    params: {
      token: sessionStorage.getItem('sidepanel_token')
    }
  }));
};

ws.onmessage = (event) => {
  const msg = JSON.parse(event.data);
  handleMessage(msg);
};

ws.onclose = (event) => {
  console.log('Connection closed:', event.code, event.reason);
  scheduleReconnect();
};

ws.onerror = (error) => {
  console.error('WebSocket error:', error);
};
```

### Reconnection Strategy

```typescript
class WebSocketManager {
  private ws: WebSocket | null = null;
  private reconnectAttempts = 0;
  private maxAttempts = 10;
  private baseDelay = 1000;  // 1 second
  
  connect(): void {
    this.ws = new WebSocket('ws://localhost:8765/ws');
    
    this.ws.onclose = () => {
      this.scheduleReconnect();
    };
  }
  
  private scheduleReconnect(): void {
    if (this.reconnectAttempts >= this.maxAttempts) {
      console.error('Max reconnection attempts reached');
      this.emit('connection.failed');
      return;
    }
    
    // Exponential backoff with jitter
    const delay = Math.min(
      this.baseDelay * Math.pow(2, this.reconnectAttempts) + 
      Math.random() * 1000,
      30000  // Max 30 seconds
    );
    
    this.reconnectAttempts++;
    console.log(`Reconnecting in ${delay}ms (attempt ${this.reconnectAttempts})`);
    
    setTimeout(() => this.connect(), delay);
  }
  
  private onConnected(): void {
    this.reconnectAttempts = 0;
    this.emit('connection.restored');
  }
}
```

---

## Message Types

### JSON-RPC 2.0 Structure

**Request:**
```typescript
interface JsonRpcRequest {
  jsonrpc: '2.0';
  id: number | string;    // Required for requests expecting response
  method: string;
  params?: object;
}
```

**Response:**
```typescript
interface JsonRpcResponse {
  jsonrpc: '2.0';
  id: number | string;    // Matches request id
  result?: any;
  error?: JsonRpcError;
}

interface JsonRpcError {
  code: number;
  message: string;
  data?: any;
}
```

**Notification (no response expected):**
```typescript
interface JsonRpcNotification {
  jsonrpc: '2.0';
  method: string;
  params?: object;
  // No 'id' field
}
```

---

## Server → Client Messages (Notifications)

### Balance Update

Sent whenever Venice balance changes.

```typescript
{
  jsonrpc: '2.0',
  method: 'balance.update',
  params: {
    diem: 42.5,
    usd: 10.0,
    effective: 52.5,
    metrics: {
      consumptionRate: 2.3,      // Diem per hour
      timeToDepletion: 18540000, // ms until depleted
      todayUsed: 7.5,
      projectedBalance: 35.2
    },
    timestamp: '2026-01-16T15:30:00.000Z'
  }
}
```

### Session Update

Sent on any session state change.

```typescript
{
  jsonrpc: '2.0',
  method: 'session.update',
  params: {
    id: 'sess_abc123',
    promptTokens: 15234,
    completionTokens: 8721,
    totalTokens: 23955,
    cost: 0.0143,
    model: 'llama-3.3-70b',
    messageCount: 12,
    updatedAt: '2026-01-16T15:30:00.000Z'
  }
}
```

### Token Usage

Sent after each message completion with token details.

```typescript
{
  jsonrpc: '2.0',
  method: 'usage.update',
  params: {
    messageId: 'msg_xyz789',
    promptTokens: 1234,
    completionTokens: 567,
    cost: 0.00089,
    model: 'llama-3.3-70b',
    duration: 3420,  // ms
    timestamp: '2026-01-16T15:30:00.000Z'
  }
}
```

### Proof Status (Lean4)

Sent when Lean4 goal state changes.

```typescript
{
  jsonrpc: '2.0',
  method: 'proof.update',
  params: {
    file: '/project/src/Theorem.lean',
    position: { line: 42, column: 5 },
    goals: [
      {
        type: '⊢ ∀ n : Nat, fibonacci n ≤ 2^n',
        context: [
          { name: 'n', type: 'Nat' },
          { name: 'ih', type: 'fibonacci n ≤ 2^n' }
        ]
      }
    ],
    diagnostics: [
      {
        severity: 'error',
        message: 'unsolved goals',
        range: { start: { line: 42, col: 0 }, end: { line: 42, col: 10 } }
      }
    ],
    suggestedTactics: [
      { tactic: 'induction n', confidence: 0.94 },
      { tactic: 'simp [fib_succ]', confidence: 0.72 }
    ]
  }
}
```

### Tool Timing

Sent after each tool execution for performance tracking.

```typescript
{
  jsonrpc: '2.0',
  method: 'tool.timing',
  params: {
    tool: 'file_read',
    duration: 23,  // ms
    success: true,
    timestamp: '2026-01-16T15:30:00.000Z'
  }
}
```

### Rate Limit Warning

Sent when approaching or hitting rate limits.

```typescript
{
  jsonrpc: '2.0',
  method: 'ratelimit.warning',
  params: {
    provider: 'venice',
    tier: 'M',
    remaining: {
      requests: 5,
      tokens: 50000
    },
    reset: '2026-01-16T15:31:00.000Z',
    severity: 'warning'  // 'warning' | 'critical' | 'blocked'
  }
}
```

### Snapshot Created

Sent when a state snapshot is saved.

```typescript
{
  jsonrpc: '2.0',
  method: 'snapshot.created',
  params: {
    id: 'snap_abc123',
    timestamp: '2026-01-16T15:30:00.000Z',
    trigger: 'auto',  // 'auto' | 'manual' | 'pre-edit'
    description: 'Before file edit: src/main.ts'
  }
}
```

---

## Client → Server Messages (Requests)

### Get Full State

Request current state for initial sync or reconnection.

```typescript
// Request
{
  jsonrpc: '2.0',
  id: 1,
  method: 'state.get',
  params: {}
}

// Response
{
  jsonrpc: '2.0',
  id: 1,
  result: {
    balance: { diem: 42.5, usd: 10.0, effective: 52.5 },
    session: { id: 'sess_abc', tokens: 23955, cost: 0.0143 },
    countdown: { hours: 8, minutes: 30, seconds: 0 },
    proof: { goals: [], diagnostics: [] },
    connected: true
  }
}
```

### Restore Snapshot

Restore to a previous state snapshot.

```typescript
// Request
{
  jsonrpc: '2.0',
  id: 2,
  method: 'snapshot.restore',
  params: {
    snapshotId: 'snap_abc123'
  }
}

// Response
{
  jsonrpc: '2.0',
  id: 2,
  result: {
    success: true,
    restored: {
      timestamp: '2026-01-16T14:00:00.000Z',
      sessionState: { /* ... */ }
    }
  }
}
```

### List Snapshots

Get available snapshots for time-travel.

```typescript
// Request
{
  jsonrpc: '2.0',
  id: 3,
  method: 'snapshot.list',
  params: {
    limit: 50,
    since: '2026-01-16T00:00:00.000Z'
  }
}

// Response
{
  jsonrpc: '2.0',
  id: 3,
  result: {
    snapshots: [
      { id: 'snap_1', timestamp: '...', trigger: 'auto', description: '...' },
      { id: 'snap_2', timestamp: '...', trigger: 'manual', description: '...' }
    ]
  }
}
```

### Set Alert Threshold

Configure alert thresholds.

```typescript
// Request
{
  jsonrpc: '2.0',
  id: 4,
  method: 'alerts.configure',
  params: {
    diemWarningPercent: 0.20,
    diemCriticalPercent: 0.05,
    depletionWarningHours: 2
  }
}

// Response
{
  jsonrpc: '2.0',
  id: 4,
  result: { success: true }
}
```

### Export Session

Export session data for sharing/review.

```typescript
// Request
{
  jsonrpc: '2.0',
  id: 5,
  method: 'session.export',
  params: {
    sessionId: 'sess_abc123',
    format: 'json',  // 'json' | 'markdown' | 'html'
    includeTimeline: true
  }
}

// Response
{
  jsonrpc: '2.0',
  id: 5,
  result: {
    data: '{ ... }',
    filename: 'session_2026-01-16.json'
  }
}
```

### Trigger Lean Check

Manually trigger Lean4 proof check.

```typescript
// Request
{
  jsonrpc: '2.0',
  id: 6,
  method: 'lean.check',
  params: {
    file: '/project/src/Theorem.lean',
    position: { line: 42, column: 5 }
  }
}

// Response
{
  jsonrpc: '2.0',
  id: 6,
  result: {
    goals: [ /* ... */ ],
    diagnostics: [ /* ... */ ]
  }
}
```

---

## Error Codes

### Standard JSON-RPC Errors

| Code | Message | Description |
|------|---------|-------------|
| -32700 | Parse error | Invalid JSON |
| -32600 | Invalid Request | Not valid JSON-RPC |
| -32601 | Method not found | Unknown method |
| -32602 | Invalid params | Invalid parameters |
| -32603 | Internal error | Server error |

### Custom Error Codes

| Code | Message | Description |
|------|---------|-------------|
| -32000 | Not authenticated | Auth required |
| -32001 | Snapshot not found | Invalid snapshot ID |
| -32002 | Session not found | Invalid session ID |
| -32003 | Lean unavailable | Lean LSP not connected |
| -32004 | Venice unavailable | Venice API unreachable |
| -32005 | Rate limited | Too many requests |

### Error Response Example

```typescript
{
  jsonrpc: '2.0',
  id: 5,
  error: {
    code: -32001,
    message: 'Snapshot not found',
    data: {
      snapshotId: 'snap_invalid',
      availableSnapshots: 42
    }
  }
}
```

---

## PureScript WebSocket Client

### Type Definitions

```purescript
module Sidepanel.WebSocket where

import Prelude
import Data.Argonaut (class DecodeJson, class EncodeJson, Json)
import Data.Either (Either)
import Effect.Aff (Aff)

-- JSON-RPC types
type JsonRpcRequest =
  { jsonrpc :: String
  , id :: Int
  , method :: String
  , params :: Json
  }

type JsonRpcResponse =
  { jsonrpc :: String
  , id :: Int
  , result :: Maybe Json
  , error :: Maybe JsonRpcError
  }

type JsonRpcNotification =
  { jsonrpc :: String
  , method :: String
  , params :: Json
  }

type JsonRpcError =
  { code :: Int
  , message :: String
  , data :: Maybe Json
  }

-- Message type union
data ServerMessage
  = BalanceUpdate BalanceParams
  | SessionUpdate SessionParams
  | UsageUpdate UsageParams
  | ProofUpdate ProofParams
  | ToolTiming ToolTimingParams
  | RateLimitWarning RateLimitParams
  | SnapshotCreated SnapshotParams

derive instance genericServerMessage :: Generic ServerMessage _
instance decodeServerMessage :: DecodeJson ServerMessage where
  decodeJson = genericDecodeJson
```

### Client Implementation

```purescript
module Sidepanel.WebSocket.Client where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Ref (Ref, new, read, write)
import Web.Socket.WebSocket as WS

type WSClient =
  { socket :: WS.WebSocket
  , nextId :: Ref Int
  , pending :: Ref (Map Int (Json -> Effect Unit))
  }

createClient :: String -> Effect WSClient
createClient url = do
  socket <- WS.create url []
  nextId <- new 1
  pending <- new Map.empty
  pure { socket, nextId, pending }

-- Send request and await response
request :: forall a. EncodeJson a => DecodeJson a 
        => WSClient -> String -> Json -> Aff a
request client method params = makeAff \cb -> do
  id <- read client.nextId
  write (id + 1) client.nextId
  
  -- Register callback
  callbacks <- read client.pending
  write (Map.insert id (cb <<< decodeJson) callbacks) client.pending
  
  -- Send request
  let req = { jsonrpc: "2.0", id, method, params }
  WS.sendString client.socket (stringify req)
  
  -- Return canceller
  pure $ effectCanceler do
    callbacks' <- read client.pending
    write (Map.delete id callbacks') client.pending

-- Subscribe to notifications
subscribe :: WSClient -> (ServerMessage -> Effect Unit) -> Effect Unit
subscribe client handler = do
  WS.onMessage client.socket \event -> do
    let msg = parseMessage event.data
    case msg of
      Left err -> Console.error $ "Parse error: " <> err
      Right (Notification notif) -> handler notif
      Right (Response resp) -> do
        callbacks <- read client.pending
        case Map.lookup resp.id callbacks of
          Just cb -> cb resp.result
          Nothing -> Console.warn $ "Orphan response: " <> show resp.id
```

---

## Heartbeat / Keep-Alive

### Ping/Pong

```typescript
// Server sends ping every 30 seconds
{
  jsonrpc: '2.0',
  method: 'ping',
  params: { timestamp: 1705423800000 }
}

// Client responds with pong
{
  jsonrpc: '2.0',
  method: 'pong',
  params: { timestamp: 1705423800000 }
}
```

### Connection Health

```typescript
// Server tracks last pong time
// If no pong within 60 seconds, close connection

// Client tracks last ping time
// If no ping within 60 seconds, attempt reconnect
```

---

## Security Considerations

### Authentication Token

```typescript
// Token generated when OpenCode starts
// Stored in session storage, not persistent
// Required for all connections

// Token validation
{
  jsonrpc: '2.0',
  id: 1,
  method: 'auth.validate',
  params: { token: 'random_token_here' }
}

// Success
{
  jsonrpc: '2.0',
  id: 1,
  result: { valid: true, expires: '2026-01-16T23:59:59Z' }
}
```

### Message Size Limits

- Maximum message size: 1 MB
- Reject messages exceeding limit
- Large data (exports) chunked into multiple messages

### Rate Limiting

- Max 100 messages per second per client
- Exceeding triggers temporary block
- Prevents DoS on bridge server

---

## Testing

### Mock Server for Tests

```typescript
import { WebSocketServer } from 'ws';

function createMockBridge(port: number): MockBridge {
  const wss = new WebSocketServer({ port });
  const messages: any[] = [];
  
  wss.on('connection', (ws) => {
    ws.on('message', (data) => {
      const msg = JSON.parse(data.toString());
      messages.push(msg);
      
      // Auto-respond to requests
      if (msg.id) {
        ws.send(JSON.stringify({
          jsonrpc: '2.0',
          id: msg.id,
          result: getMockResult(msg.method)
        }));
      }
    });
  });
  
  return {
    broadcast: (msg: any) => {
      wss.clients.forEach(client => {
        client.send(JSON.stringify(msg));
      });
    },
    getMessages: () => messages,
    close: () => wss.close()
  };
}
```

---

## Related Specifications

- `30-BRIDGE-ARCHITECTURE.md` - Bridge server design
- `32-STATE-SYNCHRONIZATION.md` - State sync patterns
- `43-WEBSOCKET-CLIENT.md` - PureScript client component

---

*"The protocol is the contract. Break the contract, break the trust."*
