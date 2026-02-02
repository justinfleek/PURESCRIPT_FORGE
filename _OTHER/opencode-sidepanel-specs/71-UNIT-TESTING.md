# 71-UNIT-TESTING: Test Patterns and Examples

## Overview

This document provides concrete patterns for writing unit tests across the codebase, covering PureScript (purescript-spec), TypeScript (Vitest), and property-based testing.

---

## PureScript Testing with purescript-spec

### Test Structure

```purescript
module Test.Sidepanel.State.BalanceSpec where

import Prelude
import Test.Spec (Spec, describe, it, pending)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy, fail)
import Test.Spec.QuickCheck (quickCheck)
import Sidepanel.State.Balance

spec :: Spec Unit
spec = describe "Balance State" do
  describe "mergeBalance" do
    it "merges partial updates correctly" do
      let 
        current = { diem: 50.0, usd: 10.0, effective: 60.0, lastUpdated: someTime }
        update = { diem: Just 45.0, usd: Nothing, effective: Nothing, lastUpdated: Nothing }
        result = mergeBalance current update
      
      result.diem `shouldEqual` 45.0
      result.usd `shouldEqual` 10.0  -- Unchanged
      result.effective `shouldEqual` 60.0  -- Unchanged
    
    it "updates all fields when provided" do
      let 
        current = defaultBalance
        update = { diem: Just 42.0, usd: Just 8.0, effective: Just 50.0, lastUpdated: Just newTime }
        result = mergeBalance current update
      
      result.diem `shouldEqual` 42.0
      result.usd `shouldEqual` 8.0
      result.effective `shouldEqual` 50.0
  
  describe "calculateAlertLevel" do
    it "returns Critical when diem is zero" do
      calculateAlertLevel { diem: 0.0, hoursRemaining: 0.0 } `shouldEqual` Critical
    
    it "returns Critical when diem < 1" do
      calculateAlertLevel { diem: 0.5, hoursRemaining: 10.0 } `shouldEqual` Critical
    
    it "returns Warning when diem < 5" do
      calculateAlertLevel { diem: 4.0, hoursRemaining: 10.0 } `shouldEqual` Warning
    
    it "returns Warning when hours remaining < 2" do
      calculateAlertLevel { diem: 20.0, hoursRemaining: 1.5 } `shouldEqual` Warning
    
    it "returns Normal for healthy balance" do
      calculateAlertLevel { diem: 50.0, hoursRemaining: 20.0 } `shouldEqual` Normal
  
  describe "formatDiem" do
    it "formats whole numbers without decimals" do
      formatDiem 42.0 `shouldEqual` "42"
    
    it "formats decimals to 2 places" do
      formatDiem 42.567 `shouldEqual` "42.57"
    
    it "handles zero" do
      formatDiem 0.0 `shouldEqual` "0"
```

### Testing Reducers

```purescript
module Test.Sidepanel.State.ReducerSpec where

import Prelude
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Sidepanel.State.Reducer (reduce)
import Sidepanel.State.AppState (initialState)
import Sidepanel.State.Actions

spec :: Spec Unit
spec = describe "State Reducer" do
  describe "UpdateBalance" do
    it "updates balance state" do
      let 
        state = initialState
        action = UpdateBalance { diem: Just 42.0, usd: Nothing, effective: Nothing, lastUpdated: Nothing }
        result = reduce state action
      
      result.balance.diem `shouldEqual` 42.0
    
    it "preserves other state" do
      let 
        state = initialState { connected = true }
        action = UpdateBalance { diem: Just 42.0, usd: Nothing, effective: Nothing, lastUpdated: Nothing }
        result = reduce state action
      
      result.connected `shouldEqual` true
  
  describe "SetConnected" do
    it "sets connected to true" do
      let result = reduce initialState (SetConnected true)
      result.connected `shouldEqual` true
    
    it "sets connected to false" do
      let 
        state = initialState { connected = true }
        result = reduce state (SetConnected false)
      result.connected `shouldEqual` false
  
  describe "FullSync" do
    it "replaces entire state" do
      let 
        newState = initialState { connected = true, balance = { diem: 100.0, usd: 20.0, effective: 120.0, lastUpdated: someTime } }
        result = reduce initialState (FullSync newState)
      
      result `shouldEqual` newState
```

### Testing Components (with Halogen.Test.Driver)

```purescript
module Test.Sidepanel.Components.CountdownSpec where

import Prelude
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Halogen.Test.Driver as TD
import Sidepanel.Components.Balance.Countdown as Countdown

spec :: Spec Unit  
spec = describe "Countdown Component" do
  it "renders time correctly" do
    io <- TD.runUI Countdown.component { timezone: Nothing }
    
    -- Query component for rendered time
    state <- TD.getState io
    
    state.timeRemaining.hours `shouldSatisfy` (_ >= 0)
    state.timeRemaining.minutes `shouldSatisfy` (_ >= 0)
    state.timeRemaining.seconds `shouldSatisfy` (_ >= 0)
  
  it "updates urgency level based on time" do
    io <- TD.runUI Countdown.component { timezone: Nothing }
    
    -- Simulate time update
    TD.send io Countdown.Tick
    
    state <- TD.getState io
    -- Urgency should be calculated
    state.urgencyLevel `shouldSatisfy` isValidUrgency

isValidUrgency :: UrgencyLevel -> Boolean
isValidUrgency = case _ of
  Normal -> true
  Warning -> true
  Critical -> true
```

### Property-Based Testing

```purescript
module Test.Sidepanel.Property.BalanceProps where

import Prelude
import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck)
import Test.QuickCheck (class Arbitrary, arbitrary, (===), (==>))
import Sidepanel.State.Balance

spec :: Spec Unit
spec = describe "Balance Properties" do
  it "effective = diem + usd" $ quickCheck \diem usd ->
    let balance = { diem, usd, effective: diem + usd, lastUpdated: defaultTime }
    in balance.effective === balance.diem + balance.usd
  
  it "merge preserves unspecified fields" $ quickCheck \current ->
    let 
      update = { diem: Nothing, usd: Nothing, effective: Nothing, lastUpdated: Nothing }
      result = mergeBalance current update
    in result === current
  
  it "alert level is monotonic with balance" $ quickCheck \diem1 diem2 hours ->
    diem1 >= 0.0 && diem2 >= 0.0 && hours >= 0.0 ==>
      let 
        level1 = calculateAlertLevel { diem: diem1, hoursRemaining: hours }
        level2 = calculateAlertLevel { diem: diem2, hoursRemaining: hours }
      in diem1 <= diem2 ==> severityGte level1 level2

severityGte :: AlertLevel -> AlertLevel -> Boolean
severityGte Critical _ = true
severityGte Warning Warning = true
severityGte Warning Normal = true
severityGte Normal Normal = true
severityGte _ _ = false
```

---

## TypeScript Testing with Vitest

### Test Structure

```typescript
// bridge/test/unit/venice/balance.test.ts
import { describe, it, expect, beforeEach } from 'vitest';
import { extractBalance, calculateConsumptionRate } from '../../../src/venice/balance';

describe('Balance Extraction', () => {
  describe('extractBalance', () => {
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
    
    it('handles missing USD header', () => {
      const headers = new Headers({
        'x-venice-balance-diem': '42.5'
      });
      
      const balance = extractBalance(headers);
      
      expect(balance.diem).toBe(42.5);
      expect(balance.usd).toBeNull();
    });
    
    it('returns null for missing diem header', () => {
      const headers = new Headers({});
      
      const balance = extractBalance(headers);
      
      expect(balance).toBeNull();
    });
    
    it('handles malformed header values', () => {
      const headers = new Headers({
        'x-venice-balance-diem': 'not-a-number'
      });
      
      const balance = extractBalance(headers);
      
      expect(balance).toBeNull();
    });
  });
  
  describe('calculateConsumptionRate', () => {
    it('calculates rate from snapshots', () => {
      const now = Date.now();
      const snapshots = [
        { timestamp: new Date(now - 60 * 60 * 1000), diem: 50 },  // 1 hour ago
        { timestamp: new Date(now - 30 * 60 * 1000), diem: 48 },  // 30 min ago
        { timestamp: new Date(now), diem: 45 }                     // Now
      ];
      
      const rate = calculateConsumptionRate(snapshots);
      
      // Consumed 5 diem in 1 hour = 5/hr
      expect(rate).toBeCloseTo(5, 1);
    });
    
    it('returns 0 for insufficient snapshots', () => {
      const snapshots = [{ timestamp: new Date(), diem: 50 }];
      
      const rate = calculateConsumptionRate(snapshots);
      
      expect(rate).toBe(0);
    });
    
    it('handles balance resets', () => {
      const now = Date.now();
      const snapshots = [
        { timestamp: new Date(now - 60 * 60 * 1000), diem: 10 },
        { timestamp: new Date(now - 30 * 60 * 1000), diem: 100 },  // Reset!
        { timestamp: new Date(now), diem: 95 }
      ];
      
      const rate = calculateConsumptionRate(snapshots);
      
      // Should only count from after reset
      expect(rate).toBeCloseTo(10, 1);  // 5 diem in 30 min = 10/hr
    });
  });
});
```

### Testing WebSocket Handlers

```typescript
// bridge/test/unit/websocket/handlers.test.ts
import { describe, it, expect, vi, beforeEach } from 'vitest';
import { handleStateGet, handleBalanceRefresh } from '../../../src/websocket/handlers';
import { createMockStore, createMockClient } from '../../fixtures/mocks';

describe('WebSocket Handlers', () => {
  let store: MockStore;
  let client: MockClient;
  
  beforeEach(() => {
    store = createMockStore();
    client = createMockClient();
  });
  
  describe('handleStateGet', () => {
    it('returns full state', async () => {
      store.setState({
        connected: true,
        balance: { diem: 42, usd: 10, effective: 52 }
      });
      
      const response = await handleStateGet(store, client, {
        jsonrpc: '2.0',
        id: 1,
        method: 'state.get',
        params: {}
      });
      
      expect(response.result.connected).toBe(true);
      expect(response.result.balance.diem).toBe(42);
    });
    
    it('includes timestamp', async () => {
      const response = await handleStateGet(store, client, {
        jsonrpc: '2.0',
        id: 1,
        method: 'state.get',
        params: {}
      });
      
      expect(response.result.timestamp).toBeDefined();
      expect(new Date(response.result.timestamp)).toBeInstanceOf(Date);
    });
  });
  
  describe('handleBalanceRefresh', () => {
    it('triggers balance update', async () => {
      const refreshSpy = vi.spyOn(store, 'refreshBalance');
      
      await handleBalanceRefresh(store, client, {
        jsonrpc: '2.0',
        id: 1,
        method: 'balance.refresh',
        params: {}
      });
      
      expect(refreshSpy).toHaveBeenCalled();
    });
  });
});
```

### Testing Rate Limiter

```typescript
// bridge/test/unit/venice/rate-limiter.test.ts
import { describe, it, expect, vi, beforeEach, afterEach } from 'vitest';
import { RateLimiter } from '../../../src/venice/rate-limiter';

describe('RateLimiter', () => {
  let limiter: RateLimiter;
  
  beforeEach(() => {
    vi.useFakeTimers();
    limiter = new RateLimiter();
  });
  
  afterEach(() => {
    vi.useRealTimers();
  });
  
  describe('acquire', () => {
    it('allows request when under limit', async () => {
      limiter.updateLimits(createHeaders({ remaining: 50 }));
      
      await expect(limiter.acquire()).resolves.toBeUndefined();
    });
    
    it('waits when limit exhausted', async () => {
      limiter.updateLimits(createHeaders({ 
        remaining: 0, 
        reset: Math.floor(Date.now() / 1000) + 30 
      }));
      
      const acquirePromise = limiter.acquire();
      
      // Should not resolve immediately
      await vi.advanceTimersByTimeAsync(1000);
      expect(limiter.getState().requestsRemaining).toBe(0);
      
      // Advance past reset
      await vi.advanceTimersByTimeAsync(30000);
      await acquirePromise;
    });
  });
  
  describe('handleRateLimited', () => {
    it('applies exponential backoff', () => {
      limiter.handleRateLimited(30);
      expect(limiter.getState().backoffRemaining).toBeGreaterThan(0);
      
      // Second limit should increase backoff
      limiter.handleRateLimited(30);
      const firstBackoff = limiter.getState().backoffRemaining;
      
      limiter.handleRateLimited(30);
      expect(limiter.getState().backoffRemaining).toBeGreaterThan(firstBackoff);
    });
  });
});

function createHeaders(opts: { remaining?: number; reset?: number }): Headers {
  return new Headers({
    'x-ratelimit-remaining-requests': String(opts.remaining ?? 60),
    'x-ratelimit-reset-requests': String(opts.reset ?? Math.floor(Date.now() / 1000) + 60)
  });
}
```

---

## Test Fixtures

### PureScript Fixtures

```purescript
module Test.Fixtures where

import Prelude
import Data.DateTime (DateTime)
import Data.DateTime.Instant (instant, toDateTime)
import Data.Maybe (fromJust)
import Data.Time.Duration (Milliseconds(..))
import Partial.Unsafe (unsafePartial)

-- Fixed timestamp for deterministic tests
testTime :: DateTime
testTime = unsafePartial $ fromJust $ toDateTime <$> instant (Milliseconds 1705330800000.0)

-- Default balance state
defaultBalance :: BalanceState
defaultBalance =
  { diem: 100.0
  , usd: 0.0
  , effective: 100.0
  , lastUpdated: testTime
  , history: []
  , metrics: defaultMetrics
  , alertLevel: Normal
  }

defaultMetrics :: BalanceMetrics
defaultMetrics =
  { consumptionRate: 0.0
  , timeToDepletion: Nothing
  , todayUsed: 0.0
  , averageDaily: 0.0
  }

-- Session fixtures
emptySession :: SessionState
emptySession =
  { id: "test-session"
  , model: "test-model"
  , provider: "test"
  , startedAt: testTime
  , messages: []
  , promptTokens: 0
  , completionTokens: 0
  , cost: 0.0
  }
```

### TypeScript Fixtures

```typescript
// bridge/test/fixtures/mocks.ts
import { vi } from 'vitest';

export function createMockStore() {
  let state = initialState();
  
  return {
    getState: vi.fn(() => state),
    setState: (newState: Partial<AppState>) => {
      state = { ...state, ...newState };
    },
    updateBalance: vi.fn((update) => {
      state.balance = { ...state.balance, ...update };
    }),
    refreshBalance: vi.fn()
  };
}

export function createMockClient() {
  return {
    id: 'test-client',
    isAuthenticated: true,
    send: vi.fn(),
    close: vi.fn()
  };
}

export function createMockWebSocket() {
  return {
    send: vi.fn(),
    close: vi.fn(),
    readyState: 1,  // OPEN
    addEventListener: vi.fn(),
    removeEventListener: vi.fn()
  };
}

// Test data generators
export function generateSnapshots(count: number, startDiem: number = 100): BalanceSnapshot[] {
  const now = Date.now();
  const interval = 60 * 60 * 1000 / count;  // Spread over 1 hour
  
  return Array.from({ length: count }, (_, i) => ({
    timestamp: new Date(now - (count - i) * interval),
    diem: startDiem - (i * 2)  // Decrease by 2 each time
  }));
}
```

---

## Running Tests

```bash
# All tests
just test

# PureScript only
just test-ps

# TypeScript only  
just test-ts

# Watch mode
just test-watch

# Coverage
just test-coverage
```

---

## Related Specifications

- `70-TESTING-STRATEGY.md` - Overall strategy
- `72-INTEGRATION-TESTING.md` - Integration tests
- `73-E2E-TESTING.md` - End-to-end tests

---

*"Tests are the specification that never lies."*
