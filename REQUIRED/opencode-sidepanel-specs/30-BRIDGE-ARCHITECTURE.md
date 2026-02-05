# 30-BRIDGE-ARCHITECTURE: Node.js Middleware Design

## Overview

The Bridge Server is the central coordination layer connecting OpenCode (plugin events), Venice API (AI inference + balance), Lean LSP (proof checking), and the browser client (WebSocket). This document details its architecture.

---

## Why a Bridge Server?

Direct browser → Venice API communication has problems:
1. **CORS** - Venice API may not allow browser origins
2. **Security** - API key would be visible in browser DevTools
3. **Rate limiting** - Browser refresh = new connection = rate limit issues
4. **Aggregation** - Need to combine multiple data sources

The Bridge solves all of these by acting as a trusted intermediary on localhost.

---

## High-Level Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           BRIDGE SERVER                                  │
│                                                                          │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐              │
│  │   HTTP       │    │  WebSocket   │    │   State      │              │
│  │   Server     │    │   Server     │    │   Store      │              │
│  │   :8765      │    │   :8765/ws   │    │              │              │
│  └──────┬───────┘    └──────┬───────┘    └──────┬───────┘              │
│         │                   │                   │                        │
│         ▼                   ▼                   ▼                        │
│  ┌─────────────────────────────────────────────────────────────────┐   │
│  │                        EVENT BUS                                 │   │
│  │  - Plugin events from OpenCode                                   │   │
│  │  - Balance updates from Venice                                   │   │
│  │  - Proof updates from Lean LSP                                   │   │
│  │  - Commands from browser                                         │   │
│  └─────────────────────────────────────────────────────────────────┘   │
│         │                   │                   │                        │
│         ▼                   ▼                   ▼                        │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐              │
│  │   OpenCode   │    │   Venice     │    │   Lean       │              │
│  │   Client     │    │   Proxy      │    │   Proxy      │              │
│  └──────────────┘    └──────────────┘    └──────────────┘              │
│                                                                          │
└──────────────────────────────────────────────────────────────────────────┘
           │                   │                   │
           ▼                   ▼                   ▼
      OpenCode             Venice API         Lean LSP
      (TUI)               (External)          (Local)
```

---

## Core Components

### 1. HTTP Server

Handles static file serving and health checks.

```typescript
// src/server.ts
import express from 'express';
import { createServer } from 'http';

export function createHttpServer(config: Config) {
  const app = express();
  
  // Health check
  app.get('/health', (req, res) => {
    res.json({ 
      status: 'ok',
      uptime: process.uptime(),
      connections: wsManager.getConnectionCount()
    });
  });
  
  // Static files (frontend bundle)
  app.use(express.static(config.staticDir));
  
  // SPA fallback
  app.get('*', (req, res) => {
    res.sendFile(path.join(config.staticDir, 'index.html'));
  });
  
  return createServer(app);
}
```

### 2. WebSocket Server

Manages browser connections and JSON-RPC communication.

```typescript
// src/websocket/manager.ts
import { WebSocketServer, WebSocket } from 'ws';

export class WebSocketManager {
  private wss: WebSocketServer;
  private clients: Map<string, ClientConnection> = new Map();
  
  constructor(server: Server) {
    this.wss = new WebSocketServer({ server, path: '/ws' });
    this.wss.on('connection', this.handleConnection.bind(this));
  }
  
  private handleConnection(ws: WebSocket, req: IncomingMessage) {
    const clientId = generateId();
    const client = new ClientConnection(clientId, ws);
    
    // Authenticate within timeout
    const authTimeout = setTimeout(() => {
      ws.close(4002, 'Authentication timeout');
    }, 5000);
    
    ws.on('message', async (data) => {
      try {
        const msg = JSON.parse(data.toString());
        
        if (msg.method === 'auth') {
          clearTimeout(authTimeout);
          await this.authenticateClient(client, msg.params);
        } else {
          await this.handleMessage(client, msg);
        }
      } catch (error) {
        this.sendError(ws, null, error);
      }
    });
    
    ws.on('close', () => {
      this.clients.delete(clientId);
    });
    
    this.clients.set(clientId, client);
  }
  
  // Broadcast to all connected clients
  broadcast(message: ServerMessage): void {
    const json = JSON.stringify(message);
    for (const client of this.clients.values()) {
      if (client.isAuthenticated && client.ws.readyState === WebSocket.OPEN) {
        client.ws.send(json);
      }
    }
  }
  
  getConnectionCount(): number {
    return this.clients.size;
  }
}
```

### 3. State Store

Central state management with event emission.

```typescript
// src/state/store.ts
import { EventEmitter } from 'events';

export interface AppState {
  connected: boolean;
  balance: BalanceState;
  session: SessionState | null;
  proof: ProofState;
  metrics: UsageMetrics;
}

export class StateStore extends EventEmitter {
  private state: AppState;
  
  constructor() {
    super();
    this.state = initialState();
  }
  
  getState(): AppState {
    return { ...this.state };
  }
  
  updateBalance(balance: Partial<BalanceState>): void {
    this.state.balance = { ...this.state.balance, ...balance };
    this.emit('balance.update', this.state.balance);
  }
  
  updateSession(session: Partial<SessionState>): void {
    this.state.session = { ...this.state.session, ...session } as SessionState;
    this.emit('session.update', this.state.session);
  }
  
  updateProof(proof: Partial<ProofState>): void {
    this.state.proof = { ...this.state.proof, ...proof };
    this.emit('proof.update', this.state.proof);
  }
  
  // Subscribe to state changes
  onStateChange(handler: (state: AppState) => void): () => void {
    const listener = () => handler(this.getState());
    this.on('balance.update', listener);
    this.on('session.update', listener);
    this.on('proof.update', listener);
    
    return () => {
      this.off('balance.update', listener);
      this.off('session.update', listener);
      this.off('proof.update', listener);
    };
  }
}
```

### 4. OpenCode Client

Connects to OpenCode via SDK and forwards events.

```typescript
// src/opencode/client.ts
import { OpenCodeClient } from '@opencode-ai/sdk';

export async function createOpenCodeClient(store: StateStore): Promise<OpenCodeClient> {
  const client = new OpenCodeClient();
  
  // Session events
  client.on('session.created', ({ session }) => {
    store.updateSession({
      id: session.id,
      promptTokens: 0,
      completionTokens: 0,
      cost: 0,
      model: session.model,
      startedAt: new Date()
    });
  });
  
  client.on('session.updated', ({ session }) => {
    store.updateSession({
      promptTokens: session.promptTokens,
      completionTokens: session.completionTokens,
      cost: session.cost
    });
  });
  
  // Message events
  client.on('message.completed', ({ message }) => {
    if (message.usage) {
      // Update session totals
      const current = store.getState().session;
      if (current) {
        store.updateSession({
          promptTokens: current.promptTokens + message.usage.promptTokens,
          completionTokens: current.completionTokens + message.usage.completionTokens,
          cost: current.cost + calculateCost(message.usage, message.model)
        });
      }
    }
  });
  
  // Tool events for timing
  client.on('tool.execute.after', ({ tool, duration }) => {
    store.recordToolTiming(tool, duration);
  });
  
  await client.connect();
  return client;
}
```

### 5. Venice Proxy

Proxies Venice API requests and extracts balance from headers.

```typescript
// src/venice/proxy.ts
import { z } from 'zod';

export class VeniceProxy {
  private apiKey: string;
  private store: StateStore;
  private rateLimiter: RateLimiter;
  
  constructor(apiKey: string, store: StateStore) {
    this.apiKey = apiKey;
    this.store = store;
    this.rateLimiter = new RateLimiter();
  }
  
  async chat(request: ChatRequest): Promise<ChatResponse> {
    await this.rateLimiter.acquire();
    
    const response = await fetch('https://api.venice.ai/api/v1/chat/completions', {
      method: 'POST',
      headers: {
        'Authorization': `Bearer ${this.apiKey}`,
        'Content-Type': 'application/json'
      },
      body: JSON.stringify(request)
    });
    
    // Extract balance from EVERY response
    this.extractAndUpdateBalance(response.headers);
    
    if (!response.ok) {
      throw await this.handleError(response);
    }
    
    return response.json();
  }
  
  private extractAndUpdateBalance(headers: Headers): void {
    const diem = parseFloat(headers.get('x-venice-balance-diem') ?? '');
    const usd = parseFloat(headers.get('x-venice-balance-usd') ?? '');
    
    if (!isNaN(diem)) {
      this.store.updateBalance({
        diem,
        usd: isNaN(usd) ? this.store.getState().balance.usd : usd,
        effective: diem + (isNaN(usd) ? this.store.getState().balance.usd : usd),
        lastUpdated: new Date()
      });
    }
    
    // Also extract rate limit info
    const remainingRequests = parseInt(headers.get('x-ratelimit-remaining-requests') ?? '');
    const remainingTokens = parseInt(headers.get('x-ratelimit-remaining-tokens') ?? '');
    
    if (!isNaN(remainingRequests) && !isNaN(remainingTokens)) {
      this.rateLimiter.updateLimits(remainingRequests, remainingTokens);
    }
  }
  
  private async handleError(response: Response): Promise<VeniceApiError> {
    const body = await response.json().catch(() => ({}));
    return new VeniceApiError(
      response.status,
      body.error?.type ?? 'unknown',
      body.error?.message ?? 'Unknown error'
    );
  }
}
```

### 6. Lean LSP Proxy

Forwards Lean4 LSP requests via MCP.

```typescript
// src/lean/proxy.ts
import { MCPClient } from '@modelcontextprotocol/sdk/client';

export class LeanProxy {
  private mcp: MCPClient;
  private store: StateStore;
  
  constructor(store: StateStore) {
    this.store = store;
    this.mcp = new MCPClient();
  }
  
  async connect(command: string, args: string[]): Promise<void> {
    await this.mcp.connect({
      command,
      args,
      transport: 'stdio'
    });
    
    this.store.updateProof({ connected: true });
  }
  
  async getGoals(file: string, line: number, column: number): Promise<ProofGoal[]> {
    const result = await this.mcp.callTool('lean_goal', {
      file,
      line,
      column
    });
    
    const goals = parseGoals(result);
    this.store.updateProof({ goals });
    return goals;
  }
  
  async getDiagnostics(file: string): Promise<Diagnostic[]> {
    const result = await this.mcp.callTool('lean_diagnostic_messages', { file });
    
    const diagnostics = parseDiagnostics(result);
    this.store.updateProof({ diagnostics });
    return diagnostics;
  }
  
  async getCompletions(file: string, line: number, column: number): Promise<Completion[]> {
    const result = await this.mcp.callTool('lean_completions', {
      file,
      line,
      column
    });
    
    return parseCompletions(result);
  }
}
```

---

## Event Flow

### Plugin Event → Browser Update

```
OpenCode         Bridge                    Browser
   │                │                         │
   │ session.updated│                         │
   ├───────────────►│                         │
   │                │ Update state            │
   │                │ ───────────             │
   │                │                         │
   │                │ broadcast(session.update)│
   │                ├────────────────────────►│
   │                │                         │ Update UI
   │                │                         │ ─────────
```

### Browser Command → Response

```
Browser          Bridge                    External
   │                │                         │
   │ restore.snapshot │                       │
   ├───────────────►│                         │
   │                │ Load from DB            │
   │                │ ───────────             │
   │                │                         │
   │   response     │                         │
   │◄───────────────┤                         │
   │                │                         │
```

### Balance Update Flow

```
Any Venice Request
        │
        ▼
   Venice API
        │
        │ Response + Headers
        ▼
   VeniceProxy.extractAndUpdateBalance()
        │
        │ store.updateBalance()
        ▼
   StateStore
        │
        │ emit('balance.update')
        ▼
   WebSocketManager.broadcast()
        │
        ▼
   All Browser Clients
```

---

## Error Handling

### Error Propagation

```typescript
// Errors are caught at boundaries and converted to appropriate responses

// HTTP boundary
app.use((error: Error, req: Request, res: Response, next: NextFunction) => {
  const appError = toAppError(error);
  logger.error('HTTP error', { error: appError });
  res.status(getHttpStatus(appError.code)).json(appError);
});

// WebSocket boundary
async function handleMessage(client: ClientConnection, msg: JsonRpcMessage) {
  try {
    const result = await processMessage(msg);
    client.send({ jsonrpc: '2.0', id: msg.id, result });
  } catch (error) {
    const appError = toAppError(error);
    logger.error('WebSocket error', { error: appError, clientId: client.id });
    client.send({ 
      jsonrpc: '2.0', 
      id: msg.id, 
      error: { code: appError.code, message: appError.message }
    });
  }
}
```

### Graceful Degradation

```typescript
// If Venice API is unavailable, we don't crash
async function getBalance(): Promise<Balance> {
  try {
    const response = await veniceProxy.ping();
    return extractBalance(response);
  } catch (error) {
    logger.warn('Venice API unavailable', { error });
    // Return last known balance
    return store.getState().balance;
  }
}

// If Lean LSP is unavailable, we continue without proofs
async function connectLean(): Promise<void> {
  try {
    await leanProxy.connect(config.leanCommand, config.leanArgs);
  } catch (error) {
    logger.warn('Lean LSP failed to connect', { error });
    store.updateProof({ connected: false });
    // Continue without Lean features
  }
}
```

---

## Configuration

```typescript
// src/config.ts
import { z } from 'zod';

const ConfigSchema = z.object({
  port: z.number().default(8765),
  host: z.string().default('127.0.0.1'),
  staticDir: z.string(),
  
  venice: z.object({
    apiKeyFile: z.string().optional(),
  }),
  
  lean: z.object({
    enabled: z.boolean().default(true),
    command: z.string().default('lean-lsp-mcp'),
    args: z.array(z.string()).default(['--transport', 'stdio']),
  }),
  
  storage: z.object({
    path: z.string(),
    encryptionKey: z.string().optional(),
  }),
  
  logging: z.object({
    level: z.enum(['debug', 'info', 'warn', 'error']).default('info'),
    format: z.enum(['json', 'pretty']).default('json'),
  }),
});

export type Config = z.infer<typeof ConfigSchema>;

export function loadConfig(): Config {
  const raw = {
    port: parseInt(process.env.SIDEPANEL_PORT ?? '8765'),
    host: process.env.SIDEPANEL_HOST ?? '127.0.0.1',
    staticDir: process.env.SIDEPANEL_STATIC_DIR ?? './dist',
    // ... load from env and config file
  };
  
  return ConfigSchema.parse(raw);
}
```

---

## Testing

### Unit Tests

```typescript
// test/unit/venice/balance.test.ts
describe('Balance Extraction', () => {
  it('extracts balance from headers', () => {
    const headers = new Headers({
      'x-venice-balance-diem': '42.5',
      'x-venice-balance-usd': '10.00'
    });
    
    const balance = extractBalance(headers);
    
    expect(balance.diem).toBe(42.5);
    expect(balance.usd).toBe(10.0);
    expect(balance.effective).toBe(52.5);
  });
});
```

### Integration Tests

```typescript
// test/integration/websocket.test.ts
describe('WebSocket Communication', () => {
  let server: Server;
  let ws: WebSocket;
  
  beforeEach(async () => {
    server = await startTestServer();
    ws = new WebSocket('ws://localhost:8765/ws');
    await waitForOpen(ws);
    await authenticate(ws);
  });
  
  afterEach(async () => {
    ws.close();
    await server.close();
  });
  
  it('broadcasts balance updates to all clients', async () => {
    const received = waitForMessage(ws, 'balance.update');
    
    // Trigger balance update
    server.emit('balance.update', { diem: 42.5, usd: 10.0 });
    
    const message = await received;
    expect(message.params.diem).toBe(42.5);
  });
});
```

---

## Related Specifications

- `31-WEBSOCKET-PROTOCOL.md` - Protocol details
- `32-STATE-SYNCHRONIZATION.md` - State sync patterns
- `10-VENICE-API-OVERVIEW.md` - Venice API integration
- `21-PLUGIN-SYSTEM.md` - OpenCode plugin events

---

*"The bridge is invisible when it works. You only notice it when it breaks."*
