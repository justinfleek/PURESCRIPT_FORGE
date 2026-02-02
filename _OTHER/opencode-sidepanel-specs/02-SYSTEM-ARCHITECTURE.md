# 02-SYSTEM-ARCHITECTURE: Component Diagrams and Data Flow

## Architecture Overview

The OpenCode Sidepanel follows a **layered client-server architecture** with clear boundaries between components. The design prioritizes:

1. **Separation of concerns:** Each layer has a single responsibility
2. **Type safety:** Interfaces verified at compile time
3. **Real-time synchronization:** Sub-50ms state propagation
4. **Graceful degradation:** Sidepanel failure doesn't break OpenCode

---

## High-Level Architecture Diagram

```
┌─────────────────────────────────────────────────────────────────────────────────┐
│                                    USER                                          │
│                    ┌──────────────────┴──────────────────┐                      │
│                    ▼                                      ▼                      │
│    ┌──────────────────────────┐          ┌──────────────────────────┐          │
│    │    Terminal (TUI)        │◄────────►│    Browser (GUI)          │          │
│    │    - OpenCode native     │  focus   │    - PureScript/Halogen   │          │
│    │    - Bubbletea rendering │  switch  │    - Real-time dashboard  │          │
│    │    - Keyboard primary    │          │    - Visual richness      │          │
│    └───────────┬──────────────┘          └───────────┬──────────────┘          │
│                │                                      │                          │
│                │ Plugin Events                        │ WebSocket                │
│                ▼                                      ▼                          │
│    ┌──────────────────────────────────────────────────────────────────┐        │
│    │                      BRIDGE SERVER (Node.js)                      │        │
│    │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────┐ │        │
│    │  │ OpenCode    │  │ WebSocket   │  │ Venice API  │  │ Lean    │ │        │
│    │  │ SDK Client  │  │ Manager     │  │ Proxy       │  │ LSP     │ │        │
│    │  └─────────────┘  └─────────────┘  └─────────────┘  └─────────┘ │        │
│    └───────────┬──────────────┬──────────────┬──────────────┬────────┘        │
│                │              │              │              │                    │
└────────────────┼──────────────┼──────────────┼──────────────┼────────────────────┘
                 │              │              │              │
                 ▼              ▼              ▼              ▼
        ┌────────────┐  ┌────────────┐  ┌────────────┐  ┌────────────┐
        │  OpenCode  │  │  Session   │  │  Venice    │  │  Lean4     │
        │  Server    │  │  Storage   │  │  API       │  │  LSP       │
        └────────────┘  └────────────┘  └────────────┘  └────────────┘
```

---

## Component Descriptions

### Layer 1: User Interfaces

#### Terminal (TUI)
**Technology:** Go + Bubbletea (OpenCode native)  
**Responsibility:** Primary interaction surface for coding tasks  
**Characteristics:**
- Full keyboard control
- Minimal resource usage
- Native terminal rendering
- Plugin hook integration for sidepanel events

**Interfaces:**
- Receives: User keystrokes, file system events
- Emits: Session events, message events, tool events via plugin hooks

#### Browser (GUI)
**Technology:** PureScript + Halogen  
**Responsibility:** Visual dashboard and rich interaction  
**Characteristics:**
- Real-time data visualization
- Interactive charts and timelines
- Optional terminal embed (xterm.js)
- Keyboard-first despite being browser

**Interfaces:**
- Receives: State updates via WebSocket
- Emits: Commands, queries, configuration changes

### Layer 2: Bridge Server

**Technology:** Node.js + TypeScript  
**Responsibility:** Coordination between all components  
**Why Node.js:** The @opencode-ai/sdk is TypeScript; using Node.js allows direct SDK usage without FFI complexity.

#### Sub-components:

**OpenCode SDK Client**
- Connects to OpenCode server
- Subscribes to plugin events
- Forwards session/message/tool events to WebSocket

**WebSocket Manager**
- Maintains connections to browser clients
- Broadcasts state updates
- Handles reconnection gracefully
- JSON-RPC 2.0 protocol

**Venice API Proxy**
- Forwards requests to Venice API
- Extracts balance headers from responses
- Aggregates usage metrics
- Handles rate limiting and backoff

**Lean LSP Proxy**
- Connects to lean-lsp-mcp server
- Translates LSP messages for browser
- Caches diagnostic state
- Forwards proof goal updates

### Layer 3: External Services

**OpenCode Server**
- Existing OpenCode backend
- No modifications required
- Plugin system provides extension points

**Session Storage**
- Append-only event log (SQLite)
- State snapshots at checkpoint
- Enables time-travel debugging

**Venice API**
- AI inference endpoint
- Balance tracking via headers
- Rate limits per tier

**Lean4 LSP**
- Language server for Lean4
- Provided by lean-lsp-mcp
- Theorem proving capabilities

---

## Data Flow Diagrams

### Flow 1: Token Usage Tracking

```
User sends prompt
        │
        ▼
┌───────────────────┐
│ OpenCode Server   │
│ (processes prompt)│
└────────┬──────────┘
         │ Plugin hook: message.completed
         ▼
┌───────────────────┐
│ Sidepanel Plugin  │
│ (extracts usage)  │
└────────┬──────────┘
         │ usage: { prompt: 1234, completion: 567 }
         ▼
┌───────────────────┐
│ Bridge Server     │
│ (aggregates)      │
└────────┬──────────┘
         │ WebSocket broadcast
         ▼
┌───────────────────┐
│ Browser Client    │
│ (updates UI)      │
└───────────────────┘
         │
         ▼
    [Token counter updates]
    [Chart animates new data point]
    [Cost projection recalculates]
```

### Flow 2: Diem Balance Update

```
Any Venice API request
        │
        ▼
┌───────────────────┐
│ Bridge Server     │───────► Venice API
│ (proxy request)   │◄─────── Response + headers
└────────┬──────────┘
         │ Extract:
         │   x-venice-balance-diem
         │   x-venice-balance-usd
         │   x-ratelimit-remaining-tokens
         ▼
┌───────────────────┐
│ Balance State     │
│ (update + store)  │
└────────┬──────────┘
         │ WebSocket broadcast
         ▼
┌───────────────────┐
│ Browser Client    │
│ (Diem widget)     │
└───────────────────┘
         │
         ▼
    [Balance display updates]
    [Countdown continues]
    [Alert if below threshold]
```

### Flow 3: Lean4 Proof Status

```
User edits Lean4 file
        │
        ▼
┌───────────────────┐
│ OpenCode Server   │
│ (file change)     │
└────────┬──────────┘
         │ Plugin hook: file.write
         ▼
┌───────────────────┐
│ Bridge Server     │───────► Lean LSP MCP
│ (forward to LSP)  │◄─────── Diagnostics + Goals
└────────┬──────────┘
         │ Parse goal state
         ▼
┌───────────────────┐
│ Proof State       │
│ (update cache)    │
└────────┬──────────┘
         │ WebSocket broadcast
         ▼
┌───────────────────┐
│ Browser Client    │
│ (Proof panel)     │
└───────────────────┘
         │
         ▼
    [Goal tree updates]
    [Diagnostics display]
    [Tactic suggestions refresh]
```

### Flow 4: Time-Travel Restore

```
User clicks timeline point
        │
        ▼
┌───────────────────┐
│ Browser Client    │
│ (selects snapshot)│
└────────┬──────────┘
         │ WebSocket: restore(snapshotId)
         ▼
┌───────────────────┐
│ Bridge Server     │
│ (load snapshot)   │
└────────┬──────────┘
         │ Query session storage
         ▼
┌───────────────────┐
│ Session Storage   │
│ (retrieve state)  │
└────────┬──────────┘
         │ Full state at snapshot
         ▼
┌───────────────────┐
│ Bridge Server     │
│ (apply state)     │
└────────┬──────────┘
         │ Notify OpenCode + broadcast
         ▼
┌───────────────────┐
│ All Clients       │
│ (sync to state)   │
└───────────────────┘
```

---

## State Management

### Canonical State Location

| State Type | Owner | Sync Method |
|------------|-------|-------------|
| Session state | OpenCode Server | Plugin events |
| Usage metrics | Bridge Server | Aggregation |
| Diem balance | Bridge Server | API header extraction |
| Proof goals | Lean LSP | LSP protocol |
| UI preferences | Browser (localStorage) | Not synced |
| Session history | Session Storage | Event log |

### State Synchronization Protocol

All state updates follow this pattern:

```typescript
interface StateUpdate {
  type: 'session' | 'usage' | 'balance' | 'proof' | 'snapshot';
  timestamp: number;       // Unix ms
  sequence: number;        // Monotonic counter
  payload: unknown;        // Type-specific data
  source: 'opencode' | 'venice' | 'lean' | 'user';
}
```

**Conflict resolution:** Last-write-wins with sequence number tiebreaker.

**Consistency guarantee:** Eventually consistent within 50ms under normal conditions.

---

## Security Boundaries

```
┌─────────────────────────────────────────────────────────────────┐
│                      TRUST BOUNDARY 1                           │
│                      (User's Machine)                           │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │                   TRUST BOUNDARY 2                       │   │
│  │                   (Bridge Server)                        │   │
│  │                                                          │   │
│  │  • Holds Venice API key (encrypted at rest)             │   │
│  │  • Validates all browser commands                        │   │
│  │  • Rate limits outgoing requests                         │   │
│  │  • Sanitizes data before storage                        │   │
│  │                                                          │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                  │
│  Browser Client:                                                │
│  • No direct API access                                         │
│  • All requests via Bridge                                      │
│  • No credential storage                                        │
│                                                                  │
│  Terminal Client:                                               │
│  • Uses OpenCode's auth                                         │
│  • Plugin runs in OpenCode sandbox                              │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
                              │
                              │ HTTPS only
                              ▼
                    ┌─────────────────┐
                    │  TRUST BOUNDARY 3│
                    │  (External APIs) │
                    │                  │
                    │  Venice API      │
                    │  Lean LSP        │
                    └─────────────────┘
```

### Security Invariants

1. **No credentials in browser:** API keys never sent to browser client
2. **Proxy all external calls:** Browser cannot directly call Venice API
3. **Validate commands:** Bridge validates all commands before execution
4. **Encrypt at rest:** Session storage encrypted with user's key
5. **No telemetry:** Zero data collection without explicit opt-in

---

## Failure Modes and Recovery

### Bridge Server Crash

**Symptom:** Browser shows "Disconnected" status  
**Impact:** No real-time updates; terminal continues working  
**Recovery:**
1. Browser attempts reconnect every 2 seconds
2. On reconnect, request full state sync
3. Session storage provides recovery point

### OpenCode Plugin Failure

**Symptom:** No events reaching Bridge  
**Impact:** Stale data in browser; terminal works normally  
**Recovery:**
1. Plugin has automatic restart logic
2. Bridge detects silence and alerts user
3. Manual restart: `:OpenCodeReloadPlugins`

### Venice API Unavailable

**Symptom:** Balance stuck, API calls fail  
**Impact:** Cannot generate AI responses; balance display stale  
**Recovery:**
1. Bridge queues requests up to 30 seconds
2. Exponential backoff on retries
3. UI shows "API Unavailable" with last known balance
4. Clear indicator of stale data

### Lean LSP Crash

**Symptom:** Proof status panel shows "Disconnected"  
**Impact:** No proof checking; coding continues  
**Recovery:**
1. Bridge attempts LSP restart
2. UI shows last known state with stale indicator
3. User can manually trigger restart

### Browser Tab Closed

**Symptom:** None (browser is optional)  
**Impact:** None; terminal continues working  
**Recovery:**
1. Opening new tab reconnects immediately
2. Full state sync on connect
3. No data loss

---

## Scalability Considerations

### Single User (Primary Use Case)
- One Bridge Server per user
- One browser connection typical
- Resource usage: ~50MB Node.js process
- Suitable for: All development machines

### Multiple Browser Tabs
- Bridge handles multiple WebSocket connections
- All tabs receive same state updates
- No additional load on Venice API

### Future: Team Sharing (Not in V1)
- Would require server-side Bridge
- State sync becomes distributed system problem
- Out of scope for initial release

---

## Technology Justification

### Why Not Direct Browser → Venice API?

1. **CORS:** Venice API may not allow browser origins
2. **Security:** API key would be in browser, visible in DevTools
3. **Rate limiting:** Browser refresh = new connection = rate limit issues
4. **Aggregation:** Need server to combine multiple event sources

### Why Not WebSocket Directly from OpenCode?

1. **Plugin sandbox:** OpenCode plugins may not support raw sockets
2. **Simplicity:** SDK handles connection management
3. **Extensibility:** Bridge can add other data sources

### Why Not Electron?

1. **Resource usage:** Electron adds 100MB+ baseline
2. **Target audience:** Terminal users hate Electron
3. **Complexity:** Packaging, updates, platform issues
4. **Philosophy:** "Use the browser you already have"

---

## Interface Contracts

### Plugin → Bridge (HTTP POST to localhost)

```typescript
interface PluginEvent {
  event: string;          // 'session.updated', 'message.completed', etc.
  timestamp: number;
  data: SessionData | MessageData | ToolData;
}
```

### Bridge → Browser (WebSocket JSON-RPC)

```typescript
// Server → Client notification
interface StateNotification {
  jsonrpc: "2.0";
  method: "state.update";
  params: StateUpdate;
}

// Client → Server request
interface CommandRequest {
  jsonrpc: "2.0";
  id: number;
  method: string;         // 'restore', 'setAlert', 'exportSession'
  params: unknown;
}

// Server → Client response
interface CommandResponse {
  jsonrpc: "2.0";
  id: number;
  result?: unknown;
  error?: { code: number; message: string };
}
```

### Bridge → Venice API (HTTP)

Standard Venice API protocol. See `10-VENICE-API-OVERVIEW.md`.

### Bridge → Lean LSP (stdio via MCP)

Standard LSP protocol over MCP transport. See `61-LEAN-LSP-MCP.md`.

---

## Deployment Architecture

```
User's Machine
├── Terminal
│   └── OpenCode (with sidepanel plugin)
│
├── Bridge Server (localhost:8765)
│   ├── HTTP server (plugin events)
│   ├── WebSocket server (browser clients)
│   └── Outbound connections
│       ├── Venice API (api.venice.ai)
│       └── Lean LSP (local subprocess)
│
├── Browser (any)
│   └── localhost:8765 (sidepanel app)
│
└── Session Storage
    └── ~/.config/opencode-sidepanel/sessions/
```

**Startup sequence:**
1. User runs `opencode serve --sidepanel`
2. OpenCode loads sidepanel plugin
3. Plugin spawns Bridge Server
4. Bridge starts HTTP + WebSocket servers
5. Bridge opens browser to localhost:8765
6. Browser connects WebSocket, requests state
7. Ready for use

---

## Appendices

### A. Detailed Component Specs
- Bridge Server: `30-BRIDGE-ARCHITECTURE.md`
- PureScript App: `40-PURESCRIPT-ARCHITECTURE.md`
- Plugin System: `21-PLUGIN-SYSTEM.md`

### B. Protocol Specifications
- WebSocket Protocol: `31-WEBSOCKET-PROTOCOL.md`
- State Sync: `32-STATE-SYNCHRONIZATION.md`

### C. Security Details
- Security Model: `83-SECURITY-MODEL.md`
- Authentication: `84-AUTHENTICATION-FLOW.md`

---

*"Architecture is the art of drawing lines that split complexity into manageable pieces. Draw them in the wrong places and you're just making more mess."*
