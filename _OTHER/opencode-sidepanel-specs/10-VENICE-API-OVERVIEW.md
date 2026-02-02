# 10-VENICE-API-OVERVIEW: API Structure, Endpoints, and Authentication

## API Base Information

| Property | Value |
|----------|-------|
| Base URL | `https://api.venice.ai/api/v1` |
| Protocol | HTTPS (TLS 1.2+) |
| Format | JSON |
| Auth | Bearer token (API key) |
| Rate Limits | Per-tier (see Rate Limits section) |

---

## Authentication

### API Key Header

All requests must include the API key:

```http
Authorization: Bearer vk_your_api_key_here
```

Or using the Venice-specific header:

```http
x-api-key: vk_your_api_key_here
```

### Key Format

Venice API keys follow the pattern: `vk_[a-zA-Z0-9]{48}`

Example: `vk_abc123def456ghi789jkl012mno345pqr678stu901vwx234`

### Key Storage (Bridge Server)

```typescript
// NEVER store in code or environment variables directly
// Use system keychain

import keytar from 'keytar';

const SERVICE = 'opencode-sidepanel';
const ACCOUNT = 'venice-api-key';

async function getApiKey(): Promise<string | null> {
  return keytar.getPassword(SERVICE, ACCOUNT);
}

async function setApiKey(key: string): Promise<void> {
  await keytar.setPassword(SERVICE, ACCOUNT, key);
}

async function deleteApiKey(): Promise<boolean> {
  return keytar.deletePassword(SERVICE, ACCOUNT);
}
```

---

## Core Endpoints

### Chat Completions

**Endpoint:** `POST /chat/completions`

**Request:**
```typescript
interface ChatCompletionRequest {
  model: string;                    // e.g., "llama-3.3-70b"
  messages: Message[];              // Conversation history
  max_tokens?: number;              // Max response tokens
  temperature?: number;             // 0.0 - 2.0
  top_p?: number;                   // 0.0 - 1.0
  stream?: boolean;                 // Enable SSE streaming
  stop?: string | string[];         // Stop sequences
  presence_penalty?: number;        // -2.0 to 2.0
  frequency_penalty?: number;       // -2.0 to 2.0
}

interface Message {
  role: 'system' | 'user' | 'assistant';
  content: string;
}
```

**Response (non-streaming):**
```typescript
interface ChatCompletionResponse {
  id: string;
  object: 'chat.completion';
  created: number;                  // Unix timestamp
  model: string;
  choices: Choice[];
  usage: Usage;
}

interface Choice {
  index: number;
  message: Message;
  finish_reason: 'stop' | 'length' | 'content_filter';
}

interface Usage {
  prompt_tokens: number;
  completion_tokens: number;
  total_tokens: number;
}
```

**Response (streaming):**
```typescript
// SSE events, one per line
data: {"id":"...","object":"chat.completion.chunk","choices":[{"delta":{"content":"Hello"}}]}
data: {"id":"...","object":"chat.completion.chunk","choices":[{"delta":{"content":" world"}}]}
data: [DONE]
```

### List Models

**Endpoint:** `GET /models`

**Response:**
```typescript
interface ModelsResponse {
  object: 'list';
  data: Model[];
}

interface Model {
  id: string;                       // e.g., "llama-3.3-70b"
  object: 'model';
  created: number;
  owned_by: string;
  pricing: {
    input: number;                  // $ per 1M tokens
    output: number;                 // $ per 1M tokens
  };
  tier: 'XS' | 'S' | 'M' | 'L';
  context_length: number;
}
```

### Image Generation

**Endpoint:** `POST /images/generations`

**Request:**
```typescript
interface ImageGenerationRequest {
  model: string;                    // e.g., "fluently-xl"
  prompt: string;
  width?: number;                   // Default: 1024
  height?: number;                  // Default: 1024
  seed?: number;                    // For reproducibility
  hide_watermark?: boolean;
  return_binary?: boolean;          // Return raw image vs base64
}
```

**Response:**
```typescript
interface ImageGenerationResponse {
  images: string[];                 // Base64 encoded or URLs
  request: {
    width: number;
    height: number;
    seed: number;
    model: string;
    prompt: string;
  };
}
```

---

## Balance and Rate Limit Headers

**CRITICAL:** These headers are returned with EVERY API response.

### Response Headers

| Header | Type | Description |
|--------|------|-------------|
| `x-venice-balance-diem` | float | Current Diem balance |
| `x-venice-balance-usd` | float | Current USD credit balance |
| `x-ratelimit-limit-requests` | int | Request limit for window |
| `x-ratelimit-remaining-requests` | int | Requests remaining |
| `x-ratelimit-limit-tokens` | int | Token limit for window |
| `x-ratelimit-remaining-tokens` | int | Tokens remaining |
| `x-ratelimit-reset-requests` | ISO datetime | When request limit resets |
| `x-ratelimit-reset-tokens` | ISO datetime | When token limit resets |

### Header Extraction Pattern

```typescript
interface VeniceResponseMeta {
  balance: {
    diem: number;
    usd: number;
  };
  rateLimits: {
    requests: {
      limit: number;
      remaining: number;
      reset: Date;
    };
    tokens: {
      limit: number;
      remaining: number;
      reset: Date;
    };
  };
}

function extractMeta(headers: Headers): VeniceResponseMeta {
  return {
    balance: {
      diem: parseFloat(headers.get('x-venice-balance-diem') ?? '0'),
      usd: parseFloat(headers.get('x-venice-balance-usd') ?? '0'),
    },
    rateLimits: {
      requests: {
        limit: parseInt(headers.get('x-ratelimit-limit-requests') ?? '0'),
        remaining: parseInt(headers.get('x-ratelimit-remaining-requests') ?? '0'),
        reset: new Date(headers.get('x-ratelimit-reset-requests') ?? ''),
      },
      tokens: {
        limit: parseInt(headers.get('x-ratelimit-limit-tokens') ?? '0'),
        remaining: parseInt(headers.get('x-ratelimit-remaining-tokens') ?? '0'),
        reset: new Date(headers.get('x-ratelimit-reset-tokens') ?? ''),
      },
    },
  };
}
```

---

## Rate Limits by Tier

### Free Tier

| Limit Type | Value |
|------------|-------|
| Requests per minute | 3 |
| Tokens per minute | 30,000 |
| Requests per day | 50 |

### Paid Tier (Diem/USD)

Limits vary by model tier:

| Model Tier | RPM | TPM | RPD |
|------------|-----|-----|-----|
| XS (qwen3-4b) | 500 | 1,000,000 | 10,000 |
| S (llama-3.2-3b) | 200 | 1,000,000 | 10,000 |
| M (llama-3.3-70b) | 50 | 750,000 | 10,000 |
| L (deepseek-r1) | 20 | 500,000 | 10,000 |

### Rate Limit Handling

```typescript
interface RateLimitHandler {
  // Check if request should proceed
  canProceed(tier: string): boolean;
  
  // Get wait time if rate limited
  getWaitTime(tier: string): number;  // milliseconds
  
  // Update state from response headers
  updateFromResponse(headers: Headers): void;
  
  // Get current state for UI display
  getState(): RateLimitState;
}

// Exponential backoff on 429
async function withRetry<T>(
  fn: () => Promise<T>,
  maxRetries = 3
): Promise<T> {
  for (let i = 0; i < maxRetries; i++) {
    try {
      return await fn();
    } catch (e) {
      if (e.status === 429) {
        const waitMs = Math.pow(2, i) * 1000 + Math.random() * 1000;
        await sleep(waitMs);
        continue;
      }
      throw e;
    }
  }
  throw new Error('Max retries exceeded');
}
```

---

## Error Responses

### Error Format

```typescript
interface VeniceError {
  error: {
    type: string;
    message: string;
    code?: string;
    param?: string;
  };
}
```

### Common Error Types

| HTTP Status | Type | Description |
|-------------|------|-------------|
| 400 | `invalid_request_error` | Malformed request |
| 401 | `authentication_error` | Invalid API key |
| 403 | `permission_denied` | Key lacks permission |
| 429 | `rate_limit_error` | Rate limit exceeded |
| 500 | `server_error` | Venice internal error |
| 503 | `service_unavailable` | Venice temporarily down |

### Error Handling Pattern

```typescript
class VeniceApiError extends Error {
  constructor(
    public status: number,
    public type: string,
    message: string,
    public code?: string
  ) {
    super(message);
    this.name = 'VeniceApiError';
  }
  
  isRetryable(): boolean {
    return this.status === 429 || this.status >= 500;
  }
}

async function handleResponse(response: Response): Promise<any> {
  if (!response.ok) {
    const body = await response.json();
    throw new VeniceApiError(
      response.status,
      body.error.type,
      body.error.message,
      body.error.code
    );
  }
  return response.json();
}
```

---

## Model Pricing Reference

**Prices as of January 2026. Check Venice docs for current pricing.**

| Model ID | Tier | Input $/M | Output $/M |
|----------|------|-----------|------------|
| qwen3-4b | XS | $0.10 | $0.10 |
| qwen3-1.7b | XS | $0.10 | $0.10 |
| llama-3.2-3b | S | $0.20 | $0.20 |
| llama-3.2-1b | S | $0.20 | $0.20 |
| llama-3.3-70b | M | $0.30 | $0.60 |
| mistral-31-24b | M | $0.30 | $0.60 |
| deepseek-r1-671b | L | $0.50 | $2.00 |
| deepseek-r1-llama-70b | L | $0.50 | $2.00 |

### Cost Calculation

```typescript
function calculateCost(
  usage: Usage,
  model: string,
  pricing: Record<string, { input: number; output: number }>
): number {
  const { input, output } = pricing[model];
  const inputCost = (usage.prompt_tokens / 1_000_000) * input;
  const outputCost = (usage.completion_tokens / 1_000_000) * output;
  return inputCost + outputCost;
}

// Example: 1000 input + 500 output on llama-3.3-70b
// Input: (1000 / 1M) * $0.30 = $0.0003
// Output: (500 / 1M) * $0.60 = $0.0003
// Total: $0.0006
```

---

## Diem Balance System

### How Diem Works

1. User stakes VVV tokens
2. Staking grants daily Diem allocation
3. 1 Diem = $1 of API credit per day
4. Balance resets at **midnight UTC (00:00:00)**
5. Unused Diem does NOT roll over

### Balance Sources

| Source | Header | Notes |
|--------|--------|-------|
| Diem (staked) | `x-venice-balance-diem` | Resets daily |
| USD (deposited) | `x-venice-balance-usd` | Does not reset |

### Which Balance Is Used First?

Venice deducts from Diem first, then USD.

```typescript
// Effective balance for UI display
function getEffectiveBalance(balance: Balance): number {
  return balance.diem + balance.usd;
}

// Consumption priority explanation
function getBalanceStatus(balance: Balance): string {
  if (balance.diem > 0) {
    return `Using Diem (${balance.diem.toFixed(2)})`;
  }
  return `Using USD (${balance.usd.toFixed(2)})`;
}
```

---

## API Client Implementation

### Full Client Interface

```typescript
interface VeniceClient {
  // Core methods
  chat(request: ChatCompletionRequest): Promise<ChatCompletionResponse>;
  chatStream(request: ChatCompletionRequest): AsyncIterable<ChatChunk>;
  listModels(): Promise<Model[]>;
  generateImage(request: ImageGenerationRequest): Promise<ImageGenerationResponse>;
  
  // Balance tracking
  getBalance(): Balance;  // Returns cached value
  onBalanceUpdate(callback: (balance: Balance) => void): void;
  
  // Rate limits
  getRateLimits(): RateLimitState;
  onRateLimitUpdate(callback: (limits: RateLimitState) => void): void;
}
```

### Streaming Implementation

```typescript
async function* chatStream(
  request: ChatCompletionRequest
): AsyncIterable<ChatChunk> {
  const response = await fetch(`${BASE_URL}/chat/completions`, {
    method: 'POST',
    headers: {
      'Authorization': `Bearer ${apiKey}`,
      'Content-Type': 'application/json',
    },
    body: JSON.stringify({ ...request, stream: true }),
  });
  
  // Extract balance from headers (even on streaming)
  updateBalance(extractMeta(response.headers));
  
  const reader = response.body!.getReader();
  const decoder = new TextDecoder();
  let buffer = '';
  
  while (true) {
    const { done, value } = await reader.read();
    if (done) break;
    
    buffer += decoder.decode(value, { stream: true });
    const lines = buffer.split('\n');
    buffer = lines.pop() ?? '';
    
    for (const line of lines) {
      if (line.startsWith('data: ')) {
        const data = line.slice(6);
        if (data === '[DONE]') return;
        yield JSON.parse(data) as ChatChunk;
      }
    }
  }
}
```

---

## Testing Venice Integration

### Mock Server for Tests

```typescript
// Use msw (Mock Service Worker) for integration tests
import { http, HttpResponse } from 'msw';
import { setupServer } from 'msw/node';

const handlers = [
  http.post('https://api.venice.ai/api/v1/chat/completions', () => {
    return HttpResponse.json(
      { /* mock response */ },
      {
        headers: {
          'x-venice-balance-diem': '42.5',
          'x-venice-balance-usd': '10.00',
        },
      }
    );
  }),
];

const server = setupServer(...handlers);

beforeAll(() => server.listen());
afterEach(() => server.resetHandlers());
afterAll(() => server.close());
```

### Balance Extraction Test

```typescript
describe('Balance Extraction', () => {
  it('extracts Diem balance from headers', () => {
    const headers = new Headers({
      'x-venice-balance-diem': '42.5',
      'x-venice-balance-usd': '10.00',
    });
    
    const meta = extractMeta(headers);
    
    expect(meta.balance.diem).toBe(42.5);
    expect(meta.balance.usd).toBe(10.0);
  });
  
  it('handles missing headers gracefully', () => {
    const headers = new Headers({});
    
    const meta = extractMeta(headers);
    
    expect(meta.balance.diem).toBe(0);
    expect(meta.balance.usd).toBe(0);
  });
});
```

---

## Related Specifications

- `11-DIEM-TRACKING.md` - Detailed Diem tracking implementation
- `12-DIEM-RESET-COUNTDOWN.md` - UTC midnight countdown
- `14-RATE-LIMIT-HANDLING.md` - Complete rate limit strategy
- `17-VENICE-ERROR-HANDLING.md` - Error taxonomy and recovery

---

*"Every API call is an opportunity to update the balance display. Never miss one."*
