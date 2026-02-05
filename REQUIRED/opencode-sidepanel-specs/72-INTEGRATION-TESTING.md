# 72-INTEGRATION-TESTING: API Contract and Component Integration Tests

## Overview

Integration tests verify that components work together correctly. They focus on the boundaries between systems: WebSocket communication, API contracts, and multi-component interactions.

---

## Test Categories

### 1. WebSocket Integration

Tests the full WebSocket communication flow between bridge and browser.

### 2. API Contract Tests

Verify that bridge API responses match expected schemas.

### 3. State Synchronization Tests

Ensure state changes propagate correctly across the system.

### 4. Plugin Integration Tests

Verify plugin events are captured and processed correctly.

---

## WebSocket Integration Tests

### Test Setup

```typescript
// bridge/test/integration/websocket.test.ts
import { describe, it, expect, beforeAll, afterAll, beforeEach } from 'vitest';
import WebSocket from 'ws';
import { createTestBridge, TestBridge } from '../fixtures/test-bridge';

describe('WebSocket Integration', () => {
  let bridge: TestBridge;
  let ws: WebSocket;
  
  beforeAll(async () => {
    bridge = await createTestBridge({ port: 0 });  // Random port
    await bridge.start();
  });
  
  afterAll(async () => {
    await bridge.stop();
  });
  
  beforeEach(async () => {
    ws = new WebSocket(`ws://localhost:${bridge.port}/ws`);
    await waitForOpen(ws);
  });
  
  afterEach(() => {
    ws.close();
  });
  
  describe('Connection', () => {
    it('establishes connection successfully', async () => {
      expect(ws.readyState).toBe(WebSocket.OPEN);
    });
    
    it('receives initial state on connect', async () => {
      const message = await waitForMessage(ws);
      
      expect(message.method).toBe('state.sync');
      expect(message.params).toHaveProperty('connected');
      expect(message.params).toHaveProperty('balance');
      expect(message.params).toHaveProperty('timestamp');
    });
    
    it('responds to ping with pong', async () => {
      const pingId = Date.now();
      
      ws.send(JSON.stringify({
        jsonrpc: '2.0',
        id: pingId,
        method: 'ping'
      }));
      
      const response = await waitForMessage(ws, m => m.id === pingId);
      
      expect(response.result).toBe('pong');
    });
    
    it('handles authentication timeout', async () => {
      // Connect without authenticating
      const unauthWs = new WebSocket(`ws://localhost:${bridge.port}/ws`);
      await waitForOpen(unauthWs);
      
      // Wait for auth timeout (default 5s)
      await delay(6000);
      
      expect(unauthWs.readyState).toBe(WebSocket.CLOSED);
    });
  });
  
  describe('State Synchronization', () => {
    it('broadcasts balance updates to all clients', async () => {
      // Connect second client
      const ws2 = new WebSocket(`ws://localhost:${bridge.port}/ws`);
      await waitForOpen(ws2);
      await authenticateClient(ws2);
      
      // Skip initial state messages
      await waitForMessage(ws2);
      
      // Trigger balance update on bridge
      bridge.updateBalance({ diem: 42.5, usd: 10.0 });
      
      // Both clients should receive update
      const [msg1, msg2] = await Promise.all([
        waitForMessage(ws, m => m.method === 'balance.update'),
        waitForMessage(ws2, m => m.method === 'balance.update')
      ]);
      
      expect(msg1.params.diem).toBe(42.5);
      expect(msg2.params.diem).toBe(42.5);
      
      ws2.close();
    });
    
    it('syncs session updates', async () => {
      // Simulate session update
      bridge.updateSession({
        id: 'test-session',
        promptTokens: 1000,
        completionTokens: 500
      });
      
      const message = await waitForMessage(ws, m => m.method === 'session.update');
      
      expect(message.params.promptTokens).toBe(1000);
      expect(message.params.completionTokens).toBe(500);
    });
  });
  
  describe('Request/Response', () => {
    it('handles state.get request', async () => {
      const response = await sendAndWait(ws, {
        method: 'state.get',
        params: {}
      });
      
      expect(response.result).toHaveProperty('connected');
      expect(response.result).toHaveProperty('balance');
      expect(response.result).toHaveProperty('session');
      expect(response.result).toHaveProperty('timestamp');
    });
    
    it('handles invalid method gracefully', async () => {
      const response = await sendAndWait(ws, {
        method: 'invalid.method',
        params: {}
      });
      
      expect(response.error).toBeDefined();
      expect(response.error.code).toBe(-32601);  // Method not found
    });
    
    it('handles malformed JSON', async () => {
      ws.send('not valid json');
      
      const message = await waitForMessage(ws, m => m.error);
      
      expect(message.error.code).toBe(-32700);  // Parse error
    });
  });
  
  describe('Reconnection', () => {
    it('client can reconnect after disconnect', async () => {
      ws.close();
      
      await delay(100);
      
      const newWs = new WebSocket(`ws://localhost:${bridge.port}/ws`);
      await waitForOpen(newWs);
      
      expect(newWs.readyState).toBe(WebSocket.OPEN);
      
      newWs.close();
    });
    
    it('receives full state on reconnect', async () => {
      // Set some state
      bridge.updateBalance({ diem: 50.0, usd: 15.0 });
      
      ws.close();
      await delay(100);
      
      const newWs = new WebSocket(`ws://localhost:${bridge.port}/ws`);
      await waitForOpen(newWs);
      
      const message = await waitForMessage(newWs);
      
      expect(message.method).toBe('state.sync');
      expect(message.params.balance.diem).toBe(50.0);
      
      newWs.close();
    });
  });
});
```

---

## API Contract Tests

### Schema Validation

```typescript
// bridge/test/integration/api-contracts.test.ts
import { describe, it, expect } from 'vitest';
import Ajv from 'ajv';
import { balanceUpdateSchema, sessionUpdateSchema, errorSchema } from '../schemas';

const ajv = new Ajv();

describe('API Contract Tests', () => {
  describe('Balance Update', () => {
    const validate = ajv.compile(balanceUpdateSchema);
    
    it('validates correct balance update', () => {
      const message = {
        jsonrpc: '2.0',
        method: 'balance.update',
        params: {
          diem: 42.5,
          usd: 10.0,
          effective: 52.5,
          lastUpdated: '2025-01-15T10:30:00Z'
        }
      };
      
      expect(validate(message)).toBe(true);
    });
    
    it('rejects invalid balance update', () => {
      const message = {
        jsonrpc: '2.0',
        method: 'balance.update',
        params: {
          diem: 'not a number'  // Should be number
        }
      };
      
      expect(validate(message)).toBe(false);
    });
    
    it('allows partial updates', () => {
      const message = {
        jsonrpc: '2.0',
        method: 'balance.update',
        params: {
          diem: 42.5  // Only diem, other fields optional
        }
      };
      
      expect(validate(message)).toBe(true);
    });
  });
  
  describe('Session Update', () => {
    const validate = ajv.compile(sessionUpdateSchema);
    
    it('validates full session update', () => {
      const message = {
        jsonrpc: '2.0',
        method: 'session.update',
        params: {
          id: 'sess_abc123',
          model: 'llama-3.3-70b',
          provider: 'venice',
          promptTokens: 15234,
          completionTokens: 8721,
          cost: 0.014,
          messageCount: 12
        }
      };
      
      expect(validate(message)).toBe(true);
    });
  });
  
  describe('Error Response', () => {
    const validate = ajv.compile(errorSchema);
    
    it('validates error response', () => {
      const message = {
        jsonrpc: '2.0',
        id: 1,
        error: {
          code: -32600,
          message: 'Invalid Request',
          data: { field: 'method' }
        }
      };
      
      expect(validate(message)).toBe(true);
    });
  });
});
```

### JSON Schemas

```typescript
// bridge/test/schemas/index.ts

export const balanceUpdateSchema = {
  type: 'object',
  required: ['jsonrpc', 'method', 'params'],
  properties: {
    jsonrpc: { const: '2.0' },
    method: { const: 'balance.update' },
    params: {
      type: 'object',
      properties: {
        diem: { type: 'number' },
        usd: { type: 'number' },
        effective: { type: 'number' },
        lastUpdated: { type: 'string', format: 'date-time' }
      },
      additionalProperties: false
    }
  }
};

export const sessionUpdateSchema = {
  type: 'object',
  required: ['jsonrpc', 'method', 'params'],
  properties: {
    jsonrpc: { const: '2.0' },
    method: { const: 'session.update' },
    params: {
      type: 'object',
      properties: {
        id: { type: 'string' },
        model: { type: 'string' },
        provider: { type: 'string' },
        promptTokens: { type: 'integer', minimum: 0 },
        completionTokens: { type: 'integer', minimum: 0 },
        cost: { type: 'number', minimum: 0 },
        messageCount: { type: 'integer', minimum: 0 }
      },
      additionalProperties: false
    }
  }
};

export const errorSchema = {
  type: 'object',
  required: ['jsonrpc', 'error'],
  properties: {
    jsonrpc: { const: '2.0' },
    id: { type: ['integer', 'string', 'null'] },
    error: {
      type: 'object',
      required: ['code', 'message'],
      properties: {
        code: { type: 'integer' },
        message: { type: 'string' },
        data: {}
      }
    }
  }
};
```

---

## Plugin Integration Tests

```typescript
// bridge/test/integration/plugin.test.ts
import { describe, it, expect, beforeAll, afterAll } from 'vitest';
import { createTestBridge, TestBridge } from '../fixtures/test-bridge';
import { MockOpenCodeClient } from '../fixtures/mock-opencode';

describe('Plugin Integration', () => {
  let bridge: TestBridge;
  let mockOpenCode: MockOpenCodeClient;
  
  beforeAll(async () => {
    mockOpenCode = new MockOpenCodeClient();
    bridge = await createTestBridge({ 
      port: 0,
      openCodeClient: mockOpenCode 
    });
    await bridge.start();
  });
  
  afterAll(async () => {
    await bridge.stop();
  });
  
  describe('Message Events', () => {
    it('captures user message event', async () => {
      const ws = await bridge.connectClient();
      
      // Simulate user message via OpenCode
      mockOpenCode.emit('message.created', {
        message: {
          id: 'msg_1',
          role: 'user',
          content: 'Hello AI'
        }
      });
      
      const message = await waitForMessage(ws, m => m.method === 'message.user');
      
      expect(message.params.content).toBe('Hello AI');
    });
    
    it('captures streaming response', async () => {
      const ws = await bridge.connectClient();
      const chunks: string[] = [];
      
      // Simulate streaming response
      mockOpenCode.emit('stream.start', { messageId: 'msg_2' });
      
      mockOpenCode.emit('stream.chunk', { messageId: 'msg_2', chunk: 'Hello' });
      mockOpenCode.emit('stream.chunk', { messageId: 'msg_2', chunk: ' world' });
      mockOpenCode.emit('stream.chunk', { messageId: 'msg_2', chunk: '!' });
      
      mockOpenCode.emit('message.completed', {
        message: {
          id: 'msg_2',
          role: 'assistant',
          content: 'Hello world!',
          usage: { promptTokens: 10, completionTokens: 5, totalTokens: 15 }
        }
      });
      
      const messages = await collectMessages(ws, 5, 1000);
      
      const startMsg = messages.find(m => m.method === 'message.assistant.start');
      const chunkMsgs = messages.filter(m => m.method === 'message.assistant.chunk');
      const completeMsg = messages.find(m => m.method === 'message.assistant.complete');
      
      expect(startMsg).toBeDefined();
      expect(chunkMsgs).toHaveLength(3);
      expect(completeMsg?.params.content).toBe('Hello world!');
    });
  });
  
  describe('Tool Events', () => {
    it('captures tool execution', async () => {
      const ws = await bridge.connectClient();
      
      // Simulate tool execution
      mockOpenCode.emit('tool.execute.before', {
        tool: 'read_file',
        args: { path: 'src/test.ts' }
      });
      
      const startMsg = await waitForMessage(ws, m => m.method === 'tool.start');
      expect(startMsg.params.tool).toBe('read_file');
      
      mockOpenCode.emit('tool.execute.after', {
        tool: 'read_file',
        args: { path: 'src/test.ts' },
        result: 'file content',
        duration: 45
      });
      
      const completeMsg = await waitForMessage(ws, m => m.method === 'tool.complete');
      expect(completeMsg.params.duration).toBe(45);
    });
  });
  
  describe('Balance Extraction', () => {
    it('extracts balance from Venice response headers', async () => {
      const ws = await bridge.connectClient();
      await skipInitialMessages(ws);
      
      // Simulate Venice response with balance headers
      mockOpenCode.emit('provider.response', {
        headers: {
          'x-venice-balance-diem': '42.5',
          'x-venice-balance-usd': '10.0'
        }
      });
      
      const message = await waitForMessage(ws, m => m.method === 'balance.update');
      
      expect(message.params.diem).toBe(42.5);
      expect(message.params.usd).toBe(10.0);
      expect(message.params.effective).toBe(52.5);
    });
  });
});
```

---

## Test Utilities

```typescript
// bridge/test/fixtures/helpers.ts

export async function waitForOpen(ws: WebSocket): Promise<void> {
  if (ws.readyState === WebSocket.OPEN) return;
  
  return new Promise((resolve, reject) => {
    ws.once('open', resolve);
    ws.once('error', reject);
    setTimeout(() => reject(new Error('Connection timeout')), 5000);
  });
}

export async function waitForMessage(
  ws: WebSocket,
  predicate: (msg: any) => boolean = () => true,
  timeout: number = 5000
): Promise<any> {
  return new Promise((resolve, reject) => {
    const timer = setTimeout(() => {
      reject(new Error('Message timeout'));
    }, timeout);
    
    const handler = (data: Buffer) => {
      const message = JSON.parse(data.toString());
      if (predicate(message)) {
        clearTimeout(timer);
        ws.off('message', handler);
        resolve(message);
      }
    };
    
    ws.on('message', handler);
  });
}

export async function sendAndWait(
  ws: WebSocket,
  request: { method: string; params: any }
): Promise<any> {
  const id = Date.now();
  
  ws.send(JSON.stringify({
    jsonrpc: '2.0',
    id,
    ...request
  }));
  
  return waitForMessage(ws, m => m.id === id);
}

export async function collectMessages(
  ws: WebSocket,
  count: number,
  timeout: number
): Promise<any[]> {
  const messages: any[] = [];
  
  return new Promise((resolve) => {
    const timer = setTimeout(() => resolve(messages), timeout);
    
    const handler = (data: Buffer) => {
      messages.push(JSON.parse(data.toString()));
      if (messages.length >= count) {
        clearTimeout(timer);
        ws.off('message', handler);
        resolve(messages);
      }
    };
    
    ws.on('message', handler);
  });
}

export function delay(ms: number): Promise<void> {
  return new Promise(resolve => setTimeout(resolve, ms));
}
```

---

## Running Integration Tests

```bash
# Run all integration tests
just test-integration

# Run with coverage
just test-integration-coverage

# Run specific test file
pnpm test bridge/test/integration/websocket.test.ts

# Run in watch mode
pnpm test:watch bridge/test/integration/
```

---

## Related Specifications

- `70-TESTING-STRATEGY.md` - Overall strategy
- `71-UNIT-TESTING.md` - Unit tests
- `73-E2E-TESTING.md` - End-to-end tests

---

*"Integration tests catch what unit tests miss."*
