# 14-RATE-LIMIT-HANDLING: Venice API Rate Limits

## Overview

Venice API enforces rate limits to ensure fair usage. The sidepanel tracks these limits, displays warnings, and implements intelligent backoff strategies.

---

## Venice Rate Limits

### Limit Types

| Tier | Requests/min | Tokens/min | Concurrent |
|------|--------------|------------|------------|
| Free | 20 | 40,000 | 2 |
| Pro | 60 | 150,000 | 5 |
| Enterprise | 300 | 1,000,000 | 20 |

### Response Headers

Every Venice API response includes rate limit info:

```
x-ratelimit-limit-requests: 60
x-ratelimit-limit-tokens: 150000
x-ratelimit-remaining-requests: 45
x-ratelimit-remaining-tokens: 125000
x-ratelimit-reset-requests: 1705330800
x-ratelimit-reset-tokens: 1705330800
```

### 429 Response

When limits exceeded:

```json
{
  "error": {
    "type": "rate_limit_error",
    "message": "Rate limit exceeded",
    "retryAfter": 30
  }
}
```

```
Retry-After: 30
```

---

## Tracking Implementation

### Rate Limit State

```typescript
// bridge/src/venice/rate-limiter.ts

interface RateLimitState {
  // Request limits
  requestLimit: number;
  requestsRemaining: number;
  requestResetTime: Date;
  
  // Token limits
  tokenLimit: number;
  tokensRemaining: number;
  tokenResetTime: Date;
  
  // Tracking
  lastUpdated: Date;
  recentRequests: RequestRecord[];  // For local tracking
}

interface RequestRecord {
  timestamp: Date;
  tokensUsed: number;
  wasLimited: boolean;
}
```

### Rate Limiter Class

```typescript
export class RateLimiter {
  private state: RateLimitState;
  private queue: RequestQueue;
  private backoffMs: number = 0;
  
  constructor() {
    this.state = this.initialState();
    this.queue = new RequestQueue();
  }
  
  // Check if we can make a request
  async acquire(estimatedTokens: number = 1000): Promise<void> {
    // Wait for any backoff
    if (this.backoffMs > 0) {
      await this.waitForBackoff();
    }
    
    // Check request limit
    if (this.state.requestsRemaining <= 0) {
      const waitMs = this.state.requestResetTime.getTime() - Date.now();
      if (waitMs > 0) {
        await delay(waitMs);
        this.resetRequestCount();
      }
    }
    
    // Check token limit
    if (this.state.tokensRemaining < estimatedTokens) {
      const waitMs = this.state.tokenResetTime.getTime() - Date.now();
      if (waitMs > 0) {
        await delay(waitMs);
        this.resetTokenCount();
      }
    }
    
    // Decrement local counters (actual values updated from response)
    this.state.requestsRemaining--;
    this.state.tokensRemaining -= estimatedTokens;
  }
  
  // Update limits from response headers
  updateLimits(headers: Headers): void {
    const requestsRemaining = parseInt(headers.get('x-ratelimit-remaining-requests') ?? '');
    const tokensRemaining = parseInt(headers.get('x-ratelimit-remaining-tokens') ?? '');
    const requestReset = parseInt(headers.get('x-ratelimit-reset-requests') ?? '');
    const tokenReset = parseInt(headers.get('x-ratelimit-reset-tokens') ?? '');
    
    if (!isNaN(requestsRemaining)) {
      this.state.requestsRemaining = requestsRemaining;
    }
    if (!isNaN(tokensRemaining)) {
      this.state.tokensRemaining = tokensRemaining;
    }
    if (!isNaN(requestReset)) {
      this.state.requestResetTime = new Date(requestReset * 1000);
    }
    if (!isNaN(tokenReset)) {
      this.state.tokenResetTime = new Date(tokenReset * 1000);
    }
    
    this.state.lastUpdated = new Date();
    this.recordRequest(false);
    this.resetBackoff();
  }
  
  // Handle rate limit error
  handleRateLimited(retryAfter: number): void {
    this.recordRequest(true);
    this.applyBackoff(retryAfter);
    
    // Broadcast warning to browser
    this.emit('ratelimit.hit', {
      retryAfter,
      requestsRemaining: this.state.requestsRemaining,
      tokensRemaining: this.state.tokensRemaining
    });
  }
  
  // Get current state for UI
  getState(): RateLimitInfo {
    return {
      requestsRemaining: this.state.requestsRemaining,
      requestLimit: this.state.requestLimit,
      requestResetIn: Math.max(0, this.state.requestResetTime.getTime() - Date.now()),
      
      tokensRemaining: this.state.tokensRemaining,
      tokenLimit: this.state.tokenLimit,
      tokenResetIn: Math.max(0, this.state.tokenResetTime.getTime() - Date.now()),
      
      isLimited: this.backoffMs > 0,
      backoffRemaining: this.backoffMs
    };
  }
  
  // Exponential backoff with jitter
  private applyBackoff(baseSeconds: number): void {
    const baseMs = baseSeconds * 1000;
    const jitter = Math.random() * 1000;  // 0-1s jitter
    
    // Increase backoff exponentially on repeated limits
    const recentLimits = this.state.recentRequests
      .filter(r => r.wasLimited && Date.now() - r.timestamp.getTime() < 60000)
      .length;
    
    const multiplier = Math.min(Math.pow(2, recentLimits), 8);  // Max 8x
    this.backoffMs = (baseMs * multiplier) + jitter;
  }
  
  private async waitForBackoff(): Promise<void> {
    if (this.backoffMs <= 0) return;
    
    await delay(this.backoffMs);
    this.backoffMs = 0;
  }
  
  private resetBackoff(): void {
    this.backoffMs = 0;
  }
  
  private recordRequest(wasLimited: boolean): void {
    this.state.recentRequests.push({
      timestamp: new Date(),
      tokensUsed: 0,  // Updated from usage
      wasLimited
    });
    
    // Keep only last 100 requests
    if (this.state.recentRequests.length > 100) {
      this.state.recentRequests = this.state.recentRequests.slice(-100);
    }
  }
}
```

---

## UI Display

### Rate Limit Indicator

```
┌─────────────────────────────────────────────────────────────────┐
│  Rate Limits                                                     │
│                                                                  │
│  Requests:  ████████████░░░░░░░░  45/60  (resets in 32s)        │
│  Tokens:    ████████████████░░░░  125K/150K  (resets in 32s)    │
│                                                                  │
│  ⚠ Rate limited - retrying in 15s                               │
└─────────────────────────────────────────────────────────────────┘
```

### PureScript Component

```purescript
module Sidepanel.Components.RateLimitIndicator where

type RateLimitInfo =
  { requestsRemaining :: Int
  , requestLimit :: Int
  , requestResetIn :: Int  -- ms
  
  , tokensRemaining :: Int
  , tokenLimit :: Int
  , tokenResetIn :: Int  -- ms
  
  , isLimited :: Boolean
  , backoffRemaining :: Int  -- ms
  }

render :: forall m. RateLimitInfo -> H.ComponentHTML Action () m
render info =
  HH.div
    [ HP.class_ (H.ClassName "rate-limit-indicator") ]
    [ HH.div
        [ HP.class_ (H.ClassName "section-title") ]
        [ HH.text "Rate Limits" ]
    
    -- Request gauge
    , renderGauge 
        "Requests"
        info.requestsRemaining
        info.requestLimit
        (formatResetTime info.requestResetIn)
    
    -- Token gauge
    , renderGauge
        "Tokens"
        info.tokensRemaining
        info.tokenLimit
        (formatResetTime info.tokenResetIn)
    
    -- Warning if rate limited
    , when info.isLimited $
        HH.div
          [ HP.class_ (H.ClassName "rate-limit-warning") ]
          [ HH.text $ "⚠ Rate limited - retrying in " <> 
                      show (info.backoffRemaining / 1000) <> "s" ]
    ]

renderGauge :: forall m. String -> Int -> Int -> String -> H.ComponentHTML Action () m
renderGauge label remaining total resetTime =
  let 
    percent = (toNumber remaining / toNumber total) * 100.0
    barClass = if percent < 20.0 then "gauge--warning" 
               else if percent < 5.0 then "gauge--critical"
               else ""
  in
    HH.div
      [ HP.class_ (H.ClassName "rate-gauge") ]
      [ HH.div
          [ HP.class_ (H.ClassName "rate-gauge__label") ]
          [ HH.text label ]
      , HH.div
          [ HP.classes [ H.ClassName "rate-gauge__bar", H.ClassName barClass ] ]
          [ HH.div
              [ HP.class_ (H.ClassName "rate-gauge__fill")
              , HP.style $ "width: " <> show percent <> "%"
              ]
              []
          ]
      , HH.div
          [ HP.class_ (H.ClassName "rate-gauge__value") ]
          [ HH.text $ formatNumber remaining <> "/" <> formatNumber total ]
      , HH.div
          [ HP.class_ (H.ClassName "rate-gauge__reset") ]
          [ HH.text $ "(resets in " <> resetTime <> ")" ]
      ]
```

---

## Proactive Limiting

### Request Queuing

When limits are low, queue requests:

```typescript
class RequestQueue {
  private queue: Array<{
    request: () => Promise<any>;
    resolve: (value: any) => void;
    reject: (error: any) => void;
  }> = [];
  
  private processing = false;
  
  async enqueue<T>(request: () => Promise<T>): Promise<T> {
    return new Promise((resolve, reject) => {
      this.queue.push({ request, resolve, reject });
      this.process();
    });
  }
  
  private async process(): Promise<void> {
    if (this.processing || this.queue.length === 0) return;
    
    this.processing = true;
    
    while (this.queue.length > 0) {
      const { request, resolve, reject } = this.queue.shift()!;
      
      try {
        // Wait for rate limiter
        await this.rateLimiter.acquire();
        
        const result = await request();
        resolve(result);
      } catch (error) {
        if (isRateLimitError(error)) {
          // Put back in queue
          this.queue.unshift({ request, resolve, reject });
          await delay(error.retryAfter * 1000);
        } else {
          reject(error);
        }
      }
    }
    
    this.processing = false;
  }
}
```

### Preemptive Warnings

```typescript
// Warn user before hitting limits
checkAndWarn(estimatedTokens: number): Warning | null {
  const state = this.getState();
  
  // Check requests
  if (state.requestsRemaining <= 5) {
    return {
      type: 'request_limit',
      message: `Only ${state.requestsRemaining} requests remaining`,
      severity: state.requestsRemaining <= 1 ? 'critical' : 'warning'
    };
  }
  
  // Check tokens
  if (state.tokensRemaining < estimatedTokens * 2) {
    return {
      type: 'token_limit',
      message: `Low token budget: ${formatNumber(state.tokensRemaining)} remaining`,
      severity: state.tokensRemaining < estimatedTokens ? 'critical' : 'warning'
    };
  }
  
  return null;
}
```

---

## WebSocket Notifications

### Rate Limit Warning

```typescript
// Sent when approaching limits
{
  jsonrpc: "2.0",
  method: "ratelimit.warning",
  params: {
    type: "requests",  // or "tokens"
    remaining: 5,
    limit: 60,
    resetIn: 32000,  // ms
    severity: "warning"
  }
}
```

### Rate Limit Hit

```typescript
// Sent when actually rate limited
{
  jsonrpc: "2.0",
  method: "ratelimit.hit",
  params: {
    retryAfter: 30,
    requestsRemaining: 0,
    tokensRemaining: 5000,
    message: "Rate limit exceeded, retrying in 30s"
  }
}
```

---

## CSS Styling

```css
.rate-limit-indicator {
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: var(--card-border-radius);
  padding: var(--space-3);
}

.rate-gauge {
  display: grid;
  grid-template-columns: 80px 1fr auto auto;
  align-items: center;
  gap: var(--space-2);
  padding: var(--space-2) 0;
}

.rate-gauge__label {
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  color: var(--color-text-secondary);
}

.rate-gauge__bar {
  height: 8px;
  background: var(--color-bg-base);
  border-radius: 4px;
  overflow: hidden;
}

.rate-gauge__fill {
  height: 100%;
  background: var(--color-success);
  transition: width var(--transition-base);
}

.rate-gauge--warning .rate-gauge__fill {
  background: var(--color-warning);
}

.rate-gauge--critical .rate-gauge__fill {
  background: var(--color-error);
}

.rate-gauge__value {
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  color: var(--color-text-primary);
  font-variant-numeric: tabular-nums;
}

.rate-gauge__reset {
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
}

.rate-limit-warning {
  margin-top: var(--space-3);
  padding: var(--space-2) var(--space-3);
  background: var(--color-warning-dim);
  border-radius: 6px;
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  color: var(--color-warning);
}
```

---

## Related Specifications

- `10-VENICE-API-OVERVIEW.md` - API structure
- `11-DIEM-TRACKING.md` - Balance tracking
- `80-ERROR-TAXONOMY.md` - Error handling

---

*"Respect the limits, or the limits will stop you."*
