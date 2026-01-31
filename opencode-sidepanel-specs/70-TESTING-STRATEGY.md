# 70-TESTING-STRATEGY: Test Pyramid and Coverage Targets

## Overview

Testing strategy for the OpenCode Sidepanel emphasizes type safety, property testing, and integration testing. PureScript's type system eliminates many bugs at compile time, so we focus tests on behavior and integration.

---

## Test Pyramid

```
                    ▲
                   /│\
                  / │ \
                 /  │  \        E2E Tests (5%)
                /   │   \       - Full user workflows
               /    │    \      - Browser automation
              /─────┼─────\
             /      │      \
            /       │       \   Integration Tests (25%)
           /        │        \  - API contracts
          /         │         \ - WebSocket flows
         /          │          \ - Plugin events
        /───────────┼───────────\
       /            │            \
      /             │             \ Unit Tests (40%)
     /              │              \ - Pure functions
    /               │               \ - State reducers
   /                │                \ - Formatters
  /─────────────────┼─────────────────\
 /                  │                  \
/                   │                   \ Type Checking (30%)
───────────────────────────────────────── - PureScript compiler
                                          - TypeScript compiler
                                          - Lean4 type checker
```

---

## Coverage Targets

| Layer | Coverage Target | Rationale |
|-------|-----------------|-----------|
| State reducers | 100% | Pure functions, critical logic |
| Formatters | 100% | Pure functions, easy to test |
| API clients | 90% | Network boundaries need coverage |
| Components | 70% | Complex state; tested via integration |
| Bridge server | 85% | Critical coordination logic |
| Plugin handlers | 80% | Event-driven, needs mocking |
| Lean4 proofs | N/A | Verified by type checker |

**Overall target:** 80% line coverage

---

## Test Categories

### Unit Tests

**What:** Pure functions, state transitions, formatting
**Tools:** purescript-spec, Vitest
**Speed:** < 1ms per test
**Isolation:** Complete - no I/O, no mocking

```purescript
-- PureScript unit test
describe "Balance Reducer" do
  it "updates balance on BalanceUpdated action" do
    let initial = { diem: 0.0, usd: 0.0 }
    let action = BalanceUpdated { diem: 42.0, usd: 10.0 }
    let result = reduce initial action
    
    result.diem `shouldEqual` 42.0
    result.usd `shouldEqual` 10.0
```

```typescript
// TypeScript unit test
describe('formatDuration', () => {
  it('formats hours and minutes', () => {
    const duration = { hours: 4, minutes: 23, seconds: 17 };
    expect(formatDuration(duration)).toBe('4h 23m');
  });
  
  it('shows only minutes when under 1 hour', () => {
    const duration = { hours: 0, minutes: 45, seconds: 30 };
    expect(formatDuration(duration)).toBe('45m');
  });
});
```

### Property Tests

**What:** Invariants that must hold for all inputs
**Tools:** purescript-quickcheck, fast-check
**Speed:** < 100ms per property (100 samples)
**Coverage:** Edge cases automatically explored

```purescript
-- PureScript property test
prop "countdown is never negative" $ \(now :: DateTime) ->
  let countdown = calculateCountdown now
  in countdown.totalSeconds >= 0

prop "effective balance = diem + usd" $ \(b :: Balance) ->
  b.effective == b.diem + b.usd

prop "consumption rate >= 0" $ \(history :: Array Snapshot) ->
  calculateRate history >= 0.0
```

```typescript
// TypeScript property test with fast-check
test.prop([fc.integer({ min: 0, max: 86400 })])('countdown formats correctly', (seconds) => {
  const formatted = formatCountdown(seconds);
  const pattern = /^\d+h \d{2}m \d{2}s$/;
  expect(formatted).toMatch(pattern);
});
```

### Integration Tests

**What:** Component interactions, API contracts, event flows
**Tools:** purescript-spec + mocks, Vitest + msw
**Speed:** < 500ms per test
**Isolation:** Mock external services

```typescript
// Bridge server integration test
describe('Venice API Proxy', () => {
  const server = setupServer(
    http.post('https://api.venice.ai/api/v1/chat/completions', () => {
      return HttpResponse.json(
        { choices: [{ message: { content: 'Hello' } }] },
        { headers: { 'x-venice-balance-diem': '42.5' } }
      );
    })
  );
  
  beforeAll(() => server.listen());
  afterEach(() => server.resetHandlers());
  afterAll(() => server.close());
  
  it('extracts balance from response headers', async () => {
    const proxy = createVeniceProxy();
    const response = await proxy.chat([{ role: 'user', content: 'Hi' }]);
    
    expect(proxy.getBalance().diem).toBe(42.5);
  });
});
```

```purescript
-- WebSocket integration test
describe "WebSocket Client" do
  it "reconnects after disconnect" do
    mockServer <- createMockServer
    client <- createClient "ws://localhost:8765"
    
    -- Verify connected
    isConnected client `shouldReturn` true
    
    -- Simulate disconnect
    mockServer.disconnect
    sleep 100
    
    -- Should auto-reconnect
    isConnected client `shouldReturn` true
```

### End-to-End Tests

**What:** Complete user workflows
**Tools:** Playwright
**Speed:** < 30s per test
**Isolation:** Full stack running

```typescript
// E2E test with Playwright
test('shows balance after connecting', async ({ page }) => {
  // Start with fresh state
  await page.goto('http://localhost:8765');
  
  // Wait for WebSocket connection
  await expect(page.locator('.connection-status')).toHaveText('Connected');
  
  // Verify balance displays
  await expect(page.locator('.diem-balance')).toBeVisible();
  await expect(page.locator('.countdown')).toBeVisible();
});

test('countdown updates every second', async ({ page }) => {
  await page.goto('http://localhost:8765');
  
  const countdown = page.locator('.countdown-time');
  const initial = await countdown.textContent();
  
  // Wait 2 seconds
  await page.waitForTimeout(2000);
  
  const updated = await countdown.textContent();
  expect(updated).not.toBe(initial);
});
```

---

## Test Organization

### Directory Structure

```
test/
├── unit/
│   ├── purescript/
│   │   ├── State/
│   │   │   ├── ReducerSpec.purs
│   │   │   └── BalanceSpec.purs
│   │   ├── Utils/
│   │   │   ├── TimeSpec.purs
│   │   │   └── CurrencySpec.purs
│   │   └── Main.purs
│   │
│   └── typescript/
│       ├── venice/
│       │   ├── client.test.ts
│       │   └── balance.test.ts
│       └── bridge/
│           └── server.test.ts
│
├── integration/
│   ├── api-proxy.test.ts
│   ├── websocket-flow.test.ts
│   └── plugin-events.test.ts
│
├── property/
│   ├── BalanceProps.purs
│   ├── CountdownProps.purs
│   └── StateProps.purs
│
├── e2e/
│   ├── balance-display.spec.ts
│   ├── countdown-timer.spec.ts
│   └── keyboard-navigation.spec.ts
│
└── fixtures/
    ├── snapshots/
    ├── mock-responses/
    └── test-data.json
```

### Naming Conventions

| Test Type | File Suffix | Example |
|-----------|-------------|---------|
| PureScript unit | `Spec.purs` | `ReducerSpec.purs` |
| TypeScript unit | `.test.ts` | `balance.test.ts` |
| Integration | `.test.ts` | `api-proxy.test.ts` |
| Property | `Props.purs` | `BalanceProps.purs` |
| E2E | `.spec.ts` | `balance-display.spec.ts` |

---

## Mocking Strategy

### External Services

```typescript
// Venice API mock
const mockVeniceHandlers = [
  http.post('https://api.venice.ai/api/v1/chat/completions', async ({ request }) => {
    const body = await request.json();
    return HttpResponse.json({
      id: 'mock-id',
      choices: [{ message: { content: 'Mock response' } }],
      usage: { prompt_tokens: 100, completion_tokens: 50 }
    }, {
      headers: {
        'x-venice-balance-diem': '42.5',
        'x-venice-balance-usd': '10.00'
      }
    });
  }),
];
```

### WebSocket Mock

```typescript
// Mock WebSocket server for testing
class MockWebSocketServer {
  private clients: Set<WebSocket> = new Set();
  
  broadcast(message: object): void {
    const json = JSON.stringify(message);
    this.clients.forEach(client => client.send(json));
  }
  
  simulateDisconnect(): void {
    this.clients.forEach(client => client.close());
  }
  
  // Get messages received from clients
  getReceivedMessages(): object[] { ... }
}
```

### OpenCode Plugin Mock

```typescript
// Mock OpenCode client for plugin testing
const mockOpenCodeClient = {
  events: new EventEmitter(),
  
  emit(event: string, data: object): void {
    this.events.emit(event, data);
  },
  
  on(event: string, handler: (data: object) => void): void {
    this.events.on(event, handler);
  }
};
```

---

## Test Data Management

### Fixtures

```typescript
// fixtures/test-data.ts
export const testBalance: Balance = {
  diem: 42.5,
  usd: 10.0,
  effective: 52.5
};

export const testSession: Session = {
  id: 'sess_test123',
  promptTokens: 1000,
  completionTokens: 500,
  cost: 0.001,
  model: 'llama-3.3-70b'
};

export const testSnapshots: Snapshot[] = [
  { id: 'snap_1', timestamp: new Date('2026-01-15T10:00:00Z'), trigger: 'auto' },
  { id: 'snap_2', timestamp: new Date('2026-01-15T11:00:00Z'), trigger: 'manual' },
];
```

### Generators (for property tests)

```purescript
-- PureScript arbitrary instances
instance arbitraryBalance :: Arbitrary Balance where
  arbitrary = do
    diem <- choose 0.0 1000.0
    usd <- choose 0.0 1000.0
    pure { diem, usd, effective: diem + usd }

instance arbitrarySnapshot :: Arbitrary Snapshot where
  arbitrary = do
    timestamp <- arbitrary
    trigger <- elements [Auto, Manual, PreEdit]
    pure { id: generateId, timestamp, trigger }
```

---

## Continuous Integration

### Test Pipeline

```yaml
# .github/workflows/test.yml
name: Tests

on: [push, pull_request]

jobs:
  unit-tests:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: cachix/install-nix-action@v24
      - run: nix develop --command just test-unit
  
  integration-tests:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: cachix/install-nix-action@v24
      - run: nix develop --command just test-integration
  
  property-tests:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: cachix/install-nix-action@v24
      - run: nix develop --command just test-property
  
  e2e-tests:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: cachix/install-nix-action@v24
      - uses: actions/setup-node@v4
      - run: npx playwright install
      - run: nix develop --command just test-e2e
  
  coverage:
    runs-on: ubuntu-latest
    needs: [unit-tests, integration-tests]
    steps:
      - uses: actions/checkout@v4
      - uses: cachix/install-nix-action@v24
      - run: nix develop --command just coverage
      - uses: codecov/codecov-action@v3
```

### Coverage Gates

```yaml
# codecov.yml
coverage:
  status:
    project:
      default:
        target: 80%
        threshold: 2%
    patch:
      default:
        target: 70%
```

---

## Performance Testing

### Latency Benchmarks

```typescript
// Benchmark state update latency
bench('state update latency', async () => {
  const start = performance.now();
  
  // Simulate state update flow
  await bridge.handleEvent({ type: 'balance.update', data: testBalance });
  
  const duration = performance.now() - start;
  expect(duration).toBeLessThan(50); // < 50ms target
});
```

### Load Testing

```typescript
// Load test WebSocket connections
test('handles 100 concurrent connections', async () => {
  const connections = await Promise.all(
    Array.from({ length: 100 }, () => createWebSocketClient())
  );
  
  // All should connect
  expect(connections.every(c => c.connected)).toBe(true);
  
  // Broadcast should reach all
  bridge.broadcast({ type: 'ping' });
  
  // Verify all received
  await Promise.all(connections.map(c => c.waitForMessage('pong')));
});
```

---

## Test Commands

```bash
# justfile

# Run all tests
test: test-unit test-integration test-property

# Unit tests
test-unit:
  spago test
  vitest run --reporter verbose

# Integration tests
test-integration:
  vitest run --config vitest.integration.config.ts

# Property tests
test-property:
  spago test --main Test.Property.Main

# E2E tests (requires running server)
test-e2e:
  playwright test

# Coverage report
coverage:
  vitest run --coverage
  spago test --main Test.Coverage.Main

# Watch mode for development
test-watch:
  vitest watch
```

---

## Related Specifications

- `71-UNIT-TESTING.md` - Detailed unit test patterns
- `72-INTEGRATION-TESTING.md` - Integration test setup
- `74-PROPERTY-TESTING.md` - Property test examples
- `75-PERFORMANCE-TESTING.md` - Benchmark configuration

---

*"Tests are not about finding bugs. They're about building confidence."*
