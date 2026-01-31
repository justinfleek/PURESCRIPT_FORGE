# 21-PLUGIN-SYSTEM: OpenCode Plugin Hooks and Lifecycle

## Overview

OpenCode's plugin system is the primary integration point for the sidepanel. Plugins receive events about session state, messages, tool executions, and file operations. This document catalogs all available hooks and our usage patterns.

**Reference:** @opencode-ai/plugin TypeScript SDK

---

## Plugin Architecture

### Plugin Definition

```typescript
import type { Plugin } from "@opencode-ai/plugin";

export const SidepanelPlugin: Plugin = async ({ client, config }) => {
  // Plugin initialization
  console.log('Sidepanel plugin initializing...');
  
  // Start bridge server
  const bridge = await startBridgeServer(config);
  
  // Return event handlers
  return {
    // Session events
    'session.created': async ({ session }) => { /* ... */ },
    'session.updated': async ({ session }) => { /* ... */ },
    'session.deleted': async ({ sessionId }) => { /* ... */ },
    
    // Message events
    'message.created': async ({ message }) => { /* ... */ },
    'message.updated': async ({ message }) => { /* ... */ },
    'message.completed': async ({ message }) => { /* ... */ },
    
    // Tool events
    'tool.execute.before': async ({ tool, args }) => { /* ... */ },
    'tool.execute.after': async ({ tool, result }) => { /* ... */ },
    
    // File events
    'file.read': async ({ path }) => { /* ... */ },
    'file.write': async ({ path, content }) => { /* ... */ },
    
    // ... more handlers
  };
};

export default SidepanelPlugin;
```

### Plugin Lifecycle

```
1. OpenCode starts
2. Loads plugin from config
3. Calls plugin factory function
4. Plugin returns event handlers
5. OpenCode wires handlers to event bus
6. Events flow as operations occur
7. On shutdown, OpenCode calls cleanup (if provided)
```

---

## Complete Event Catalog

### Session Events

| Event | Payload | When Fired |
|-------|---------|------------|
| `session.created` | `{ session: Session }` | New session started |
| `session.updated` | `{ session: Session }` | Any session property changes |
| `session.deleted` | `{ sessionId: string }` | Session closed/deleted |
| `session.switched` | `{ from: string, to: string }` | Active session changed |

**Session Object:**
```typescript
interface Session {
  id: string;
  name: string;
  createdAt: Date;
  updatedAt: Date;
  
  // Token usage for this session
  promptTokens: number;
  completionTokens: number;
  totalTokens: number;
  
  // Cost tracking (USD)
  cost: number;
  
  // Messages in session
  messageCount: number;
  
  // Model used
  model: string;
  
  // Custom metadata
  metadata: Record<string, unknown>;
}
```

**Usage for Sidepanel:**
```typescript
'session.updated': async ({ session }) => {
  // Extract usage metrics
  const usage = {
    promptTokens: session.promptTokens,
    completionTokens: session.completionTokens,
    cost: session.cost,
    model: session.model
  };
  
  // Broadcast to browser
  bridge.broadcast({
    type: 'session.update',
    data: usage,
    timestamp: Date.now()
  });
}
```

### Message Events

| Event | Payload | When Fired |
|-------|---------|------------|
| `message.created` | `{ message: Message }` | New message added |
| `message.updated` | `{ message: Message }` | Message content/status changes |
| `message.completed` | `{ message: Message }` | Message fully generated |
| `message.error` | `{ message: Message, error: Error }` | Generation failed |
| `message.cancelled` | `{ messageId: string }` | User cancelled generation |

**Message Object:**
```typescript
interface Message {
  id: string;
  sessionId: string;
  role: 'user' | 'assistant' | 'system';
  content: string;
  createdAt: Date;
  
  // For assistant messages
  status: 'pending' | 'streaming' | 'complete' | 'error';
  
  // Token usage for this message
  usage?: {
    promptTokens: number;
    completionTokens: number;
  };
  
  // Tools called during this message
  toolCalls?: ToolCall[];
  
  // Error if failed
  error?: {
    code: string;
    message: string;
  };
}
```

**Usage for Sidepanel:**
```typescript
'message.completed': async ({ message }) => {
  if (message.usage) {
    // Update running totals
    state.totalTokens += message.usage.promptTokens + message.usage.completionTokens;
    
    // Calculate cost
    const cost = calculateCost(message.usage, message.model);
    state.totalCost += cost;
    
    // Add to history for rate calculation
    state.usageHistory.push({
      timestamp: new Date(),
      tokens: message.usage.promptTokens + message.usage.completionTokens,
      cost
    });
    
    // Broadcast update
    bridge.broadcast({
      type: 'usage.update',
      data: {
        messageTokens: message.usage,
        sessionTotal: state.totalTokens,
        sessionCost: state.totalCost
      }
    });
  }
}
```

### Tool Events

| Event | Payload | When Fired |
|-------|---------|------------|
| `tool.execute.before` | `{ tool: string, args: object }` | Before tool runs |
| `tool.execute.after` | `{ tool: string, result: object, duration: number }` | After tool completes |
| `tool.execute.error` | `{ tool: string, error: Error }` | Tool execution failed |

**Usage for Performance Tracking:**
```typescript
const toolTimings: Map<string, number[]> = new Map();

'tool.execute.after': async ({ tool, result, duration }) => {
  // Track tool execution times
  if (!toolTimings.has(tool)) {
    toolTimings.set(tool, []);
  }
  toolTimings.get(tool)!.push(duration);
  
  // Broadcast for flame graph
  bridge.broadcast({
    type: 'tool.timing',
    data: {
      tool,
      duration,
      timestamp: Date.now()
    }
  });
  
  // Special handling for Lean4 MCP tools
  if (tool.startsWith('lean_')) {
    bridge.broadcast({
      type: 'lean.result',
      data: {
        tool,
        result,
        timestamp: Date.now()
      }
    });
  }
}
```

### File Events

| Event | Payload | When Fired |
|-------|---------|------------|
| `file.read` | `{ path: string, content?: string }` | File read by agent |
| `file.write` | `{ path: string, content: string }` | File written |
| `file.delete` | `{ path: string }` | File deleted |
| `file.rename` | `{ from: string, to: string }` | File renamed/moved |

**Usage for Activity Tracking:**
```typescript
'file.write': async ({ path, content }) => {
  // Log file activity
  state.fileActivity.push({
    type: 'write',
    path,
    size: content.length,
    timestamp: new Date()
  });
  
  // Check if Lean4 file
  if (path.endsWith('.lean')) {
    // Trigger proof check via MCP
    await checkLeanFile(path);
  }
  
  bridge.broadcast({
    type: 'file.activity',
    data: {
      action: 'write',
      path,
      timestamp: Date.now()
    }
  });
}
```

### Provider Events

| Event | Payload | When Fired |
|-------|---------|------------|
| `provider.request.start` | `{ provider: string, model: string }` | API request begins |
| `provider.request.end` | `{ provider: string, response: object }` | API response received |
| `provider.error` | `{ provider: string, error: Error }` | API call failed |
| `provider.rate_limited` | `{ provider: string, retryAfter: number }` | Rate limit hit |

**Usage for Venice Integration:**
```typescript
'provider.request.end': async ({ provider, response }) => {
  if (provider === 'venice') {
    // Extract balance from response headers
    // (Venice returns balance in response metadata)
    const balance = extractVeniceBalance(response);
    
    if (balance) {
      state.veniceBalance = balance;
      
      bridge.broadcast({
        type: 'balance.update',
        data: balance
      });
    }
  }
}

'provider.rate_limited': async ({ provider, retryAfter }) => {
  bridge.broadcast({
    type: 'rate_limit.hit',
    data: {
      provider,
      retryAfter,
      timestamp: Date.now()
    }
  });
}
```

### MCP Events

| Event | Payload | When Fired |
|-------|---------|------------|
| `mcp.server.connected` | `{ server: string }` | MCP server connected |
| `mcp.server.disconnected` | `{ server: string }` | MCP server disconnected |
| `mcp.tool.called` | `{ server: string, tool: string, args: object }` | MCP tool invoked |
| `mcp.tool.result` | `{ server: string, tool: string, result: object }` | MCP tool returned |

**Usage for Lean4 Integration:**
```typescript
'mcp.tool.result': async ({ server, tool, result }) => {
  if (server === 'lean-lsp') {
    switch (tool) {
      case 'lean_goal':
        bridge.broadcast({
          type: 'proof.goals',
          data: result.goals
        });
        break;
      
      case 'lean_diagnostic_messages':
        bridge.broadcast({
          type: 'proof.diagnostics',
          data: result.diagnostics
        });
        break;
      
      case 'lean_completions':
        bridge.broadcast({
          type: 'proof.completions',
          data: result.completions
        });
        break;
    }
  }
}
```

### System Events

| Event | Payload | When Fired |
|-------|---------|------------|
| `system.ready` | `{}` | OpenCode fully initialized |
| `system.shutdown` | `{}` | OpenCode shutting down |
| `system.error` | `{ error: Error }` | Unhandled error |
| `config.changed` | `{ key: string, value: unknown }` | Config updated |

---

## Plugin Configuration

### OpenCode Config (opencode.json)

```json
{
  "$schema": "https://opencode.ai/config.json",
  "plugin": ["opencode-sidepanel"],
  "mcp": {
    "lean-lsp": {
      "type": "local",
      "command": "lean-lsp-mcp",
      "args": ["--transport", "stdio"]
    }
  },
  "sidepanel": {
    "port": 8765,
    "autoOpen": true,
    "theme": "dark",
    "alerts": {
      "diemWarning": 0.20,
      "diemCritical": 0.05
    }
  }
}
```

### Plugin Package Structure

```
opencode-sidepanel/
├── package.json
├── tsconfig.json
├── src/
│   ├── index.ts          # Plugin entry point
│   ├── bridge/
│   │   ├── server.ts     # HTTP/WebSocket server
│   │   ├── handlers.ts   # WebSocket message handlers
│   │   └── state.ts      # Shared state management
│   ├── venice/
│   │   ├── client.ts     # Venice API client
│   │   ├── balance.ts    # Balance tracking
│   │   └── metrics.ts    # Usage aggregation
│   └── lean/
│       ├── proxy.ts      # Lean LSP proxy
│       └── goals.ts      # Goal state management
└── dist/                 # Compiled output
```

### Package.json

```json
{
  "name": "opencode-sidepanel",
  "version": "0.1.0",
  "main": "dist/index.js",
  "types": "dist/index.d.ts",
  "peerDependencies": {
    "@opencode-ai/plugin": "^0.x"
  },
  "dependencies": {
    "ws": "^8.x",
    "better-sqlite3": "^9.x",
    "zod": "^3.x",
    "pino": "^8.x"
  },
  "devDependencies": {
    "typescript": "^5.x",
    "@types/ws": "^8.x",
    "@types/better-sqlite3": "^7.x"
  },
  "scripts": {
    "build": "tsc",
    "dev": "tsc --watch"
  }
}
```

---

## Event Flow Diagram

```
┌─────────────────────────────────────────────────────────────────────┐
│                         OpenCode Server                              │
│                                                                      │
│  ┌──────────────┐    ┌──────────────┐    ┌──────────────┐          │
│  │   Session    │    │   Message    │    │    Tool      │          │
│  │   Manager    │    │   Handler    │    │   Executor   │          │
│  └──────┬───────┘    └──────┬───────┘    └──────┬───────┘          │
│         │                   │                   │                    │
│         │ session.*         │ message.*         │ tool.*            │
│         └───────────────────┴───────────────────┴────────────────┐  │
│                                                                  │  │
│                              Event Bus                           │  │
│                                                                  │  │
└──────────────────────────────────┬───────────────────────────────┘  │
                                   │                                   │
                                   │ All events                        │
                                   ▼                                   │
┌──────────────────────────────────────────────────────────────────────┘
│                      Sidepanel Plugin
│
│  ┌─────────────────────────────────────────────────────────────┐
│  │                    Event Handlers                            │
│  │                                                              │
│  │  session.updated ──┬──► Update session state                │
│  │  message.completed ┼──► Calculate costs, update totals      │
│  │  tool.execute.after┼──► Track timing, handle Lean4          │
│  │  provider.request  ┴──► Extract Venice balance              │
│  │                                                              │
│  └───────────────────────────┬─────────────────────────────────┘
│                              │
│                              │ Processed data
│                              ▼
│  ┌─────────────────────────────────────────────────────────────┐
│  │                    Bridge Server                             │
│  │                                                              │
│  │  State ──► WebSocket Broadcast ──► Browser Clients          │
│  │                                                              │
│  └─────────────────────────────────────────────────────────────┘
│
└─────────────────────────────────────────────────────────────────────
```

---

## Error Handling in Plugins

### Graceful Degradation

```typescript
export const SidepanelPlugin: Plugin = async ({ client }) => {
  let bridge: BridgeServer | null = null;
  
  try {
    bridge = await startBridgeServer();
  } catch (error) {
    // Log but don't crash OpenCode
    console.error('Sidepanel bridge failed to start:', error);
    // Return no-op handlers
    return {};
  }
  
  return {
    'session.updated': async ({ session }) => {
      try {
        // Handler logic
        bridge?.broadcast({ type: 'session', data: session });
      } catch (error) {
        // Log but don't propagate
        console.error('Sidepanel handler error:', error);
      }
    }
  };
};
```

### Health Checks

```typescript
// Periodic health check for bridge
setInterval(async () => {
  if (bridge && !bridge.isHealthy()) {
    console.warn('Bridge unhealthy, attempting restart...');
    try {
      await bridge.restart();
    } catch (error) {
      console.error('Bridge restart failed:', error);
    }
  }
}, 30000);  // Every 30 seconds
```

---

## Testing Plugins

### Mock Client

```typescript
import { createMockClient } from '@opencode-ai/plugin/testing';

describe('Sidepanel Plugin', () => {
  it('broadcasts session updates', async () => {
    const mockClient = createMockClient();
    const broadcasts: any[] = [];
    
    // Mock bridge
    const mockBridge = {
      broadcast: (msg: any) => broadcasts.push(msg)
    };
    
    const plugin = await SidepanelPlugin({ 
      client: mockClient,
      config: {}
    });
    
    // Simulate event
    await plugin['session.updated']?.({
      session: {
        id: 'test',
        promptTokens: 100,
        completionTokens: 50,
        cost: 0.001
      }
    });
    
    expect(broadcasts).toHaveLength(1);
    expect(broadcasts[0].type).toBe('session.update');
  });
});
```

---

## Related Specifications

- `20-OPENCODE-ARCHITECTURE.md` - OpenCode internals
- `22-SDK-INTEGRATION.md` - SDK usage patterns
- `30-BRIDGE-ARCHITECTURE.md` - Bridge server design
- `31-WEBSOCKET-PROTOCOL.md` - Message protocol

---

*"Every event is an opportunity. The plugin's job is to never miss one."*
