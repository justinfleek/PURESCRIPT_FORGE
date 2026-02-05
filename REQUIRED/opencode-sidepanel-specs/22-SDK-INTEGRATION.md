# 22-SDK-INTEGRATION: OpenCode SDK Usage

## Overview

The OpenCode SDK provides programmatic access to OpenCode's functionality. Our plugin uses the SDK to receive events, query state, and interact with sessions.

---

## SDK Installation

```bash
# In plugin directory
pnpm add @opencode-ai/sdk
```

---

## SDK Client

### Initialization

```typescript
// plugin/src/opencode/client.ts
import { OpenCodeClient, ClientConfig } from '@opencode-ai/sdk';

export async function createClient(config?: Partial<ClientConfig>): Promise<OpenCodeClient> {
  const client = new OpenCodeClient({
    // Connect to serve mode
    port: config?.port ?? 8765,
    host: config?.host ?? 'localhost',
    
    // Auto-reconnect on disconnect
    reconnect: true,
    reconnectInterval: 1000,
    maxReconnectAttempts: 10,
    
    ...config
  });
  
  await client.connect();
  return client;
}
```

### Connection Events

```typescript
const client = await createClient();

client.on('connected', () => {
  console.log('Connected to OpenCode');
});

client.on('disconnected', () => {
  console.log('Disconnected from OpenCode');
});

client.on('error', (error) => {
  console.error('SDK error:', error);
});

client.on('reconnecting', (attempt) => {
  console.log(`Reconnecting... attempt ${attempt}`);
});
```

---

## Event Subscriptions

### Session Events

```typescript
// Session created
client.on('session.created', (event: SessionCreatedEvent) => {
  const { session } = event;
  console.log('New session:', session.id);
  
  bridge.send('session.created', {
    id: session.id,
    model: session.model,
    provider: session.provider,
    createdAt: session.createdAt
  });
});

// Session updated (tokens, cost, etc.)
client.on('session.updated', (event: SessionUpdatedEvent) => {
  const { session, changes } = event;
  
  bridge.send('session.updated', {
    id: session.id,
    promptTokens: session.tokenUsage.promptTokens,
    completionTokens: session.tokenUsage.completionTokens,
    cost: session.cost,
    changes  // What specifically changed
  });
});

// Session ended
client.on('session.ended', (event: SessionEndedEvent) => {
  bridge.send('session.ended', { id: event.session.id });
});
```

### Message Events

```typescript
// Message created (user or assistant)
client.on('message.created', (event: MessageCreatedEvent) => {
  const { message, session } = event;
  
  bridge.send('message.created', {
    sessionId: session.id,
    message: {
      id: message.id,
      role: message.role,
      content: message.content,
      createdAt: message.createdAt
    }
  });
});

// Message streaming (assistant response chunks)
client.on('message.delta', (event: MessageDeltaEvent) => {
  const { messageId, delta } = event;
  
  bridge.send('message.delta', {
    messageId,
    content: delta.content,
    // For real-time updates
  });
});

// Message completed (with usage info)
client.on('message.completed', (event: MessageCompletedEvent) => {
  const { message, usage } = event;
  
  bridge.send('message.completed', {
    id: message.id,
    content: message.content,
    usage: usage ? {
      promptTokens: usage.promptTokens,
      completionTokens: usage.completionTokens,
      totalTokens: usage.totalTokens,
      model: usage.model,
      cost: usage.cost
    } : null
  });
});
```

### Tool Events

```typescript
// Tool execution starting
client.on('tool.execute.before', (event: ToolExecuteBeforeEvent) => {
  const { tool, args, messageId } = event;
  
  bridge.send('tool.execute.before', {
    messageId,
    tool: tool.name,
    args
  });
});

// Tool execution completed
client.on('tool.execute.after', (event: ToolExecuteAfterEvent) => {
  const { tool, result, duration, messageId } = event;
  
  bridge.send('tool.execute.after', {
    messageId,
    tool: tool.name,
    result: {
      success: result.success,
      output: result.output,
      error: result.error
    },
    durationMs: duration
  });
  
  // Track tool timing for performance metrics
  store.recordToolTiming(tool.name, duration);
});

// Tool execution failed
client.on('tool.execute.error', (event: ToolExecuteErrorEvent) => {
  const { tool, error, messageId } = event;
  
  bridge.send('tool.execute.error', {
    messageId,
    tool: tool.name,
    error: error.message
  });
});
```

### Provider Events

```typescript
// Request to provider starting
client.on('provider.request.start', (event: ProviderRequestStartEvent) => {
  const { provider, model, sessionId } = event;
  
  bridge.send('provider.request.start', {
    sessionId,
    provider,
    model
  });
});

// Request to provider completed
client.on('provider.request.end', (event: ProviderRequestEndEvent) => {
  const { provider, model, duration, usage, headers } = event;
  
  // CRITICAL: Extract Venice balance from headers
  if (provider === 'venice' && headers) {
    const diem = parseFloat(headers['x-venice-balance-diem'] ?? '');
    const usd = parseFloat(headers['x-venice-balance-usd'] ?? '');
    
    if (!isNaN(diem)) {
      store.updateBalance({ diem, usd });
    }
  }
  
  bridge.send('provider.request.end', {
    provider,
    model,
    durationMs: duration,
    usage
  });
});

// Rate limit hit
client.on('provider.rate_limited', (event: ProviderRateLimitedEvent) => {
  const { provider, retryAfter } = event;
  
  bridge.send('ratelimit.hit', {
    provider,
    retryAfter
  });
});
```

### MCP Events

```typescript
// MCP server connected
client.on('mcp.server.connected', (event: MCPServerConnectedEvent) => {
  const { server, tools } = event;
  
  if (server.name === 'lean-lsp') {
    store.updateProof({ connected: true });
    bridge.send('lean.connected', { tools: tools.map(t => t.name) });
  }
});

// MCP server disconnected
client.on('mcp.server.disconnected', (event: MCPServerDisconnectedEvent) => {
  const { server } = event;
  
  if (server.name === 'lean-lsp') {
    store.updateProof({ connected: false });
    bridge.send('lean.disconnected', {});
  }
});

// MCP tool called
client.on('mcp.tool.called', (event: MCPToolCalledEvent) => {
  const { server, tool, args } = event;
  
  if (server.name === 'lean-lsp') {
    bridge.send('lean.tool.called', { tool, args });
  }
});

// MCP tool result
client.on('mcp.tool.result', (event: MCPToolResultEvent) => {
  const { server, tool, result } = event;
  
  if (server.name === 'lean-lsp' && tool === 'lean_goal') {
    // Parse and forward proof goals
    const goals = parseLeanGoals(result);
    store.updateProof({ goals });
    bridge.send('proof.update', { goals });
  }
});
```

---

## Query API

### Session Queries

```typescript
// Get current session
const session = await client.getCurrentSession();

// Get session by ID
const session = await client.getSession(sessionId);

// List recent sessions
const sessions = await client.listSessions({
  limit: 20,
  orderBy: 'updatedAt',
  order: 'desc'
});
```

### Message Queries

```typescript
// Get messages for session
const messages = await client.getMessages(sessionId, {
  limit: 100,
  includeToolCalls: true
});

// Get specific message
const message = await client.getMessage(messageId);
```

### Provider Queries

```typescript
// Get available providers
const providers = await client.getProviders();

// Get models for provider
const models = await client.getModels('venice');

// Get current provider config
const config = await client.getProviderConfig();
```

---

## SDK Types

### Core Types

```typescript
interface Session {
  id: string;
  title: string;
  model: string;
  provider: string;
  createdAt: Date;
  updatedAt: Date;
  tokenUsage: TokenUsage;
  cost: number;
}

interface Message {
  id: string;
  sessionId: string;
  role: 'user' | 'assistant' | 'system' | 'tool';
  content: string;
  toolCalls?: ToolCall[];
  toolResults?: ToolResult[];
  createdAt: Date;
  usage?: MessageUsage;
}

interface TokenUsage {
  promptTokens: number;
  completionTokens: number;
  totalTokens: number;
  cachedTokens?: number;
}

interface MessageUsage {
  promptTokens: number;
  completionTokens: number;
  model: string;
  cost: number;
}

interface ToolCall {
  id: string;
  name: string;
  arguments: Record<string, unknown>;
}

interface ToolResult {
  callId: string;
  success: boolean;
  output?: string;
  error?: string;
}
```

### Event Types

```typescript
interface SessionCreatedEvent {
  session: Session;
}

interface SessionUpdatedEvent {
  session: Session;
  changes: Array<'tokens' | 'cost' | 'title'>;
}

interface MessageCompletedEvent {
  message: Message;
  usage?: MessageUsage;
}

interface ToolExecuteAfterEvent {
  tool: { name: string; description: string };
  args: Record<string, unknown>;
  result: ToolResult;
  duration: number;  // milliseconds
  messageId: string;
}

interface ProviderRequestEndEvent {
  provider: string;
  model: string;
  duration: number;
  usage?: TokenUsage;
  headers?: Record<string, string>;  // Response headers
}
```

---

## Error Handling

```typescript
import { OpenCodeError, ConnectionError, TimeoutError } from '@opencode-ai/sdk';

try {
  const session = await client.getCurrentSession();
} catch (error) {
  if (error instanceof ConnectionError) {
    // Not connected to OpenCode
    console.error('Not connected:', error.message);
  } else if (error instanceof TimeoutError) {
    // Request timed out
    console.error('Request timed out:', error.message);
  } else if (error instanceof OpenCodeError) {
    // Generic SDK error
    console.error('SDK error:', error.code, error.message);
  } else {
    // Unknown error
    throw error;
  }
}
```

---

## Complete Plugin Example

```typescript
// plugin/src/index.ts
import { Plugin, PluginAPI } from '@opencode-ai/sdk';
import { createClient } from './opencode/client';
import { BridgeConnection } from './bridge/connection';

export class SidepanelPlugin implements Plugin {
  private client: OpenCodeClient;
  private bridge: BridgeConnection;
  
  async init(ctx: Context, api: PluginAPI): Promise<void> {
    // Connect to bridge server
    this.bridge = new BridgeConnection(8765);
    await this.bridge.connect();
    
    // Create SDK client
    this.client = await createClient();
    
    // Subscribe to all relevant events
    this.subscribeToEvents();
    
    // Initial state sync
    await this.syncInitialState();
  }
  
  private subscribeToEvents(): void {
    // Session events
    this.client.on('session.created', this.handleSessionCreated.bind(this));
    this.client.on('session.updated', this.handleSessionUpdated.bind(this));
    
    // Message events
    this.client.on('message.created', this.handleMessageCreated.bind(this));
    this.client.on('message.completed', this.handleMessageCompleted.bind(this));
    
    // Tool events
    this.client.on('tool.execute.after', this.handleToolExecuted.bind(this));
    
    // Provider events (for balance extraction)
    this.client.on('provider.request.end', this.handleProviderResponse.bind(this));
    
    // MCP events (for Lean)
    this.client.on('mcp.tool.result', this.handleMCPResult.bind(this));
  }
  
  private async syncInitialState(): Promise<void> {
    const session = await this.client.getCurrentSession();
    if (session) {
      this.bridge.send('session.sync', session);
    }
  }
  
  async shutdown(): Promise<void> {
    await this.bridge.close();
  }
}

export default SidepanelPlugin;
```

---

## Related Specifications

- `20-OPENCODE-ARCHITECTURE.md` - OpenCode structure
- `21-PLUGIN-SYSTEM.md` - Plugin events
- `30-BRIDGE-ARCHITECTURE.md` - Bridge server

---

*"The SDK is your window into OpenCode. Use it wisely."*
