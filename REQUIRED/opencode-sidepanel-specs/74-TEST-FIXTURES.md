# 74-TEST-FIXTURES: Reusable Test Data and Mocks

## Overview

Test fixtures provide consistent, reusable test data and mock objects for unit, integration, and E2E testing.

---

## Fixture Categories

1. **Data Fixtures** - Sample sessions, messages, balances
2. **Mock Services** - Fake Venice API, WebSocket
3. **Factory Functions** - Generate test data with overrides
4. **Scenarios** - Complete test scenarios

---

## Data Fixtures

### Sessions

```typescript
// test/fixtures/sessions.ts

export const FIXTURES = {
  sessions: {
    empty: {
      id: 'sess_empty',
      title: 'Empty Session',
      createdAt: new Date('2025-01-15T12:00:00Z'),
      updatedAt: new Date('2025-01-15T12:00:00Z'),
      model: 'llama-3.3-70b',
      messages: [],
      promptTokens: 0,
      completionTokens: 0,
      cost: 0
    },
    
    active: {
      id: 'sess_active',
      title: 'Debug Auth',
      createdAt: new Date('2025-01-15T12:30:00Z'),
      updatedAt: new Date('2025-01-15T13:15:00Z'),
      model: 'llama-3.3-70b',
      messages: [
        { id: 'msg_1', role: 'user', content: 'Help me debug...', sequence: 0 },
        { id: 'msg_2', role: 'assistant', content: 'I\'ll analyze...', sequence: 1 }
      ],
      promptTokens: 15234,
      completionTokens: 8721,
      cost: 0.014
    },
    
    longConversation: {
      id: 'sess_long',
      title: 'Refactoring Project',
      createdAt: new Date('2025-01-14T09:00:00Z'),
      updatedAt: new Date('2025-01-14T17:00:00Z'),
      model: 'llama-3.3-70b',
      messages: generateMessages(50),
      promptTokens: 85000,
      completionTokens: 42000,
      cost: 0.089
    }
  }
};
```

### Messages

```typescript
export const MESSAGES = {
  userSimple: {
    id: 'msg_user_1',
    role: 'user' as const,
    content: 'What is a closure in JavaScript?',
    timestamp: new Date('2025-01-15T12:30:00Z')
  },
  
  assistantWithCode: {
    id: 'msg_asst_1',
    role: 'assistant' as const,
    content: 'A closure is a function that...\n\n```javascript\nfunction outer() {...}```',
    timestamp: new Date('2025-01-15T12:30:15Z'),
    tokens: { prompt: 25, completion: 150 }
  },
  
  assistantWithToolCall: {
    id: 'msg_asst_tool',
    role: 'assistant' as const,
    content: 'Let me read that file.',
    timestamp: new Date('2025-01-15T12:31:00Z'),
    toolCalls: [{
      id: 'call_1',
      type: 'function',
      function: {
        name: 'read_file',
        arguments: '{"path": "src/auth.ts"}'
      }
    }]
  },
  
  toolResult: {
    id: 'msg_tool_1',
    role: 'tool' as const,
    content: 'export function authenticate...',
    toolCallId: 'call_1'
  }
};
```

### Balance

```typescript
export const BALANCES = {
  full: {
    diem: 100.0,
    usd: 12.34,
    burnRate: 0,
    lastUpdated: new Date('2025-01-15T00:00:00Z')
  },
  
  normal: {
    diem: 42.5,
    usd: 5.50,
    burnRate: 5.2,
    lastUpdated: new Date('2025-01-15T14:30:00Z')
  },
  
  low: {
    diem: 8.3,
    usd: 1.20,
    burnRate: 6.1,
    lastUpdated: new Date('2025-01-15T18:00:00Z')
  },
  
  critical: {
    diem: 2.1,
    usd: 0.30,
    burnRate: 8.5,
    lastUpdated: new Date('2025-01-15T22:00:00Z')
  },
  
  depleted: {
    diem: 0,
    usd: 0.15,
    burnRate: 0,
    lastUpdated: new Date('2025-01-15T23:30:00Z')
  }
};
```

---

## Factory Functions

```typescript
// test/fixtures/factories.ts

export function createSession(overrides: Partial<Session> = {}): Session {
  return {
    id: `sess_${generateId()}`,
    title: 'Test Session',
    createdAt: new Date(),
    updatedAt: new Date(),
    model: 'llama-3.3-70b',
    messages: [],
    promptTokens: 0,
    completionTokens: 0,
    cost: 0,
    branchName: 'main',
    ...overrides
  };
}

export function createMessage(overrides: Partial<Message> = {}): Message {
  return {
    id: `msg_${generateId()}`,
    role: 'user',
    content: 'Test message content',
    timestamp: new Date(),
    sequence: 0,
    ...overrides
  };
}

export function createBalance(overrides: Partial<Balance> = {}): Balance {
  return {
    diem: 50.0,
    usd: 5.00,
    burnRate: 0,
    lastUpdated: new Date(),
    ...overrides
  };
}

export function createSnapshot(overrides: Partial<Snapshot> = {}): Snapshot {
  return {
    id: `snap_${generateId()}`,
    timestamp: new Date(),
    type: 'manual',
    trigger: { type: 'manual' },
    starred: false,
    sizeBytes: 1024,
    state: {},
    summary: {},
    ...overrides
  };
}

// Generate multiple items
export function generateMessages(count: number): Message[] {
  return Array.from({ length: count }, (_, i) => createMessage({
    sequence: i,
    role: i % 2 === 0 ? 'user' : 'assistant'
  }));
}

export function generateSessions(count: number): Session[] {
  return Array.from({ length: count }, () => createSession());
}
```

---

## Mock Services

### Mock Venice API

```typescript
// test/mocks/veniceApi.ts

export class MockVeniceApi {
  private balance: Balance = BALANCES.normal;
  private responses: Map<string, any> = new Map();
  private requestLog: Request[] = [];
  
  // Configure mock responses
  setBalance(balance: Balance): void {
    this.balance = balance;
  }
  
  setResponse(model: string, response: ChatCompletion): void {
    this.responses.set(model, response);
  }
  
  setError(error: VeniceError): void {
    this.nextError = error;
  }
  
  // Mock fetch implementation
  async fetch(request: Request): Promise<Response> {
    this.requestLog.push(request);
    
    if (this.nextError) {
      const error = this.nextError;
      this.nextError = null;
      return new Response(JSON.stringify({ error }), { status: 400 });
    }
    
    const body = await request.json();
    const response = this.responses.get(body.model) ?? this.defaultResponse();
    
    return new Response(JSON.stringify(response), {
      status: 200,
      headers: {
        'x-venice-balance-diem': String(this.balance.diem),
        'x-venice-balance-usd': String(this.balance.usd),
        'x-venice-model': body.model
      }
    });
  }
  
  // Streaming mock
  async *stream(request: Request): AsyncGenerator<string> {
    const body = await request.json();
    const content = 'This is a test response.';
    
    for (const word of content.split(' ')) {
      yield `data: ${JSON.stringify({
        choices: [{ delta: { content: word + ' ' } }]
      })}\n\n`;
      await delay(50);
    }
    
    yield `data: ${JSON.stringify({
      choices: [{ delta: {}, finish_reason: 'stop' }],
      usage: { prompt_tokens: 10, completion_tokens: 5, total_tokens: 15 }
    })}\n\n`;
    
    yield 'data: [DONE]\n\n';
  }
  
  // Assertions
  getRequests(): Request[] {
    return this.requestLog;
  }
  
  getLastRequest(): Request | undefined {
    return this.requestLog[this.requestLog.length - 1];
  }
  
  assertCalled(times?: number): void {
    if (times !== undefined && this.requestLog.length !== times) {
      throw new Error(`Expected ${times} calls, got ${this.requestLog.length}`);
    }
    if (this.requestLog.length === 0) {
      throw new Error('Expected API to be called');
    }
  }
  
  reset(): void {
    this.requestLog = [];
    this.nextError = null;
  }
  
  private defaultResponse(): ChatCompletion {
    return {
      id: 'test-completion',
      object: 'chat.completion',
      created: Date.now(),
      model: 'llama-3.3-70b',
      choices: [{
        index: 0,
        message: { role: 'assistant', content: 'Test response' },
        finish_reason: 'stop'
      }],
      usage: { prompt_tokens: 10, completion_tokens: 5, total_tokens: 15 }
    };
  }
}
```

### Mock WebSocket

```typescript
// test/mocks/websocket.ts

export class MockWebSocket {
  readyState: number = WebSocket.OPEN;
  
  private messageHandlers: ((event: MessageEvent) => void)[] = [];
  private sentMessages: string[] = [];
  
  addEventListener(event: string, handler: Function): void {
    if (event === 'message') {
      this.messageHandlers.push(handler as any);
    }
  }
  
  send(data: string): void {
    this.sentMessages.push(data);
  }
  
  close(): void {
    this.readyState = WebSocket.CLOSED;
  }
  
  // Test helpers
  simulateMessage(data: any): void {
    const event = new MessageEvent('message', {
      data: JSON.stringify(data)
    });
    this.messageHandlers.forEach(h => h(event));
  }
  
  getSentMessages(): any[] {
    return this.sentMessages.map(m => JSON.parse(m));
  }
  
  getLastSentMessage(): any {
    const messages = this.getSentMessages();
    return messages[messages.length - 1];
  }
}
```

### Mock Database

```typescript
// test/mocks/database.ts

export class MockDatabase {
  private data: Map<string, Map<string, any>> = new Map();
  
  constructor() {
    this.data.set('sessions', new Map());
    this.data.set('messages', new Map());
    this.data.set('snapshots', new Map());
  }
  
  async get<T>(table: string, id: string): Promise<T | null> {
    return this.data.get(table)?.get(id) ?? null;
  }
  
  async all<T>(table: string): Promise<T[]> {
    return Array.from(this.data.get(table)?.values() ?? []);
  }
  
  async insert(table: string, item: any): Promise<void> {
    this.data.get(table)?.set(item.id, item);
  }
  
  async update(table: string, id: string, updates: any): Promise<void> {
    const existing = this.data.get(table)?.get(id);
    if (existing) {
      this.data.get(table)?.set(id, { ...existing, ...updates });
    }
  }
  
  async delete(table: string, id: string): Promise<void> {
    this.data.get(table)?.delete(id);
  }
  
  // Seed with fixtures
  seed(fixtures: { sessions?: Session[]; messages?: Message[] }): void {
    fixtures.sessions?.forEach(s => this.insert('sessions', s));
    fixtures.messages?.forEach(m => this.insert('messages', m));
  }
  
  reset(): void {
    this.data.forEach(table => table.clear());
  }
}
```

---

## Test Scenarios

```typescript
// test/scenarios/index.ts

export const SCENARIOS = {
  // New user starting fresh
  newUser: {
    balance: BALANCES.full,
    sessions: [],
    settings: DEFAULT_SETTINGS
  },
  
  // Active user mid-session
  activeSession: {
    balance: BALANCES.normal,
    sessions: [FIXTURES.sessions.active],
    currentSessionId: 'sess_active',
    settings: DEFAULT_SETTINGS
  },
  
  // User with low balance
  lowBalance: {
    balance: BALANCES.low,
    sessions: [FIXTURES.sessions.active],
    currentSessionId: 'sess_active',
    settings: DEFAULT_SETTINGS
  },
  
  // User with depleted balance
  noBalance: {
    balance: BALANCES.depleted,
    sessions: [FIXTURES.sessions.active],
    currentSessionId: 'sess_active',
    settings: DEFAULT_SETTINGS
  },
  
  // Power user with many sessions
  powerUser: {
    balance: BALANCES.normal,
    sessions: generateSessions(20),
    currentSessionId: null,
    settings: { ...DEFAULT_SETTINGS, vimMode: true }
  }
};

// Apply scenario to test environment
export function applyScenario(
  scenario: keyof typeof SCENARIOS,
  env: TestEnvironment
): void {
  const data = SCENARIOS[scenario];
  
  env.mockVeniceApi.setBalance(data.balance);
  env.mockDatabase.seed({ sessions: data.sessions });
  env.store.dispatch({ type: 'INIT', payload: data });
}
```

---

## PureScript Test Fixtures

```purescript
-- test/Fixtures.purs

module Test.Fixtures where

import Prelude

testSession :: Session
testSession =
  { id: "sess_test"
  , title: "Test Session"
  , createdAt: unsafeParseDate "2025-01-15T12:00:00Z"
  , updatedAt: unsafeParseDate "2025-01-15T12:00:00Z"
  , model: "llama-3.3-70b"
  , messages: []
  , promptTokens: 0
  , completionTokens: 0
  , cost: 0.0
  }

testBalance :: Balance
testBalance =
  { diem: 42.5
  , usd: 5.50
  , burnRate: 5.2
  , lastUpdated: unsafeParseDate "2025-01-15T14:30:00Z"
  }

testMessage :: Message
testMessage =
  { id: "msg_test"
  , role: User
  , content: "Test message"
  , timestamp: unsafeParseDate "2025-01-15T12:30:00Z"
  , sequence: 0
  }

-- Factories
mkSession :: Partial Session -> Session
mkSession overrides = merge testSession overrides

mkBalance :: Partial Balance -> Balance  
mkBalance overrides = merge testBalance overrides
```

---

## Related Specifications

- `70-TESTING-STRATEGY.md` - Overall strategy
- `71-UNIT-TESTING.md` - Unit test patterns
- `72-INTEGRATION-TESTING.md` - Integration tests

---

*"Good fixtures make good tests. Good tests make good software."*
