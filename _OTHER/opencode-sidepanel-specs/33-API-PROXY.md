# 33-API-PROXY: Venice API Communication

## Overview

The API Proxy in the bridge server handles all communication with Venice AI, including authentication, request forwarding, balance extraction, and error handling.

---

## Architecture

```
Browser         Bridge                      Venice API
   │               │                             │
   │ (no direct    │                             │
   │  access)      │                             │
   │               │ ── Request ────────────────►│
   │               │    + Authorization header   │
   │               │                             │
   │               │ ◄── Response ───────────────│
   │               │    + Balance headers        │
   │               │                             │
   │ ◄── Balance   │                             │
   │     Update    │                             │
```

### Why Proxy?

1. **Security** - API key never reaches browser
2. **Balance extraction** - Parse headers on every response
3. **Rate limit handling** - Centralized backoff logic
4. **Request queuing** - Manage concurrent requests
5. **Error normalization** - Consistent error format

---

## Implementation

### Venice Client

```typescript
// bridge/src/venice/client.ts
import { z } from 'zod';

// Request/Response schemas
const ChatRequestSchema = z.object({
  model: z.string(),
  messages: z.array(z.object({
    role: z.enum(['system', 'user', 'assistant']),
    content: z.string()
  })),
  max_tokens: z.number().optional(),
  temperature: z.number().optional(),
  stream: z.boolean().optional()
});

const ChatResponseSchema = z.object({
  id: z.string(),
  object: z.literal('chat.completion'),
  model: z.string(),
  choices: z.array(z.object({
    message: z.object({
      role: z.string(),
      content: z.string()
    }),
    finish_reason: z.string()
  })),
  usage: z.object({
    prompt_tokens: z.number(),
    completion_tokens: z.number(),
    total_tokens: z.number()
  })
});

export class VeniceClient {
  private baseUrl = 'https://api.venice.ai/api/v1';
  private apiKey: string;
  private rateLimiter: RateLimiter;
  private store: StateStore;
  
  constructor(config: VeniceConfig, store: StateStore) {
    this.apiKey = config.apiKey;
    this.rateLimiter = new RateLimiter();
    this.store = store;
  }
  
  async chat(request: ChatRequest): Promise<ChatResponse> {
    // Validate request
    const validated = ChatRequestSchema.parse(request);
    
    // Estimate tokens for rate limiting
    const estimatedTokens = this.estimateTokens(validated);
    
    // Wait for rate limiter
    await this.rateLimiter.acquire(estimatedTokens);
    
    try {
      const response = await fetch(`${this.baseUrl}/chat/completions`, {
        method: 'POST',
        headers: {
          'Authorization': `Bearer ${this.apiKey}`,
          'Content-Type': 'application/json'
        },
        body: JSON.stringify(validated)
      });
      
      // ALWAYS extract balance from headers
      this.extractBalance(response.headers);
      this.extractRateLimits(response.headers);
      
      if (!response.ok) {
        throw await this.handleError(response);
      }
      
      const data = await response.json();
      return ChatResponseSchema.parse(data);
      
    } catch (error) {
      if (error instanceof VeniceApiError && error.isRateLimited) {
        this.rateLimiter.handleRateLimited(error.retryAfter ?? 30);
      }
      throw error;
    }
  }
  
  async streamChat(request: ChatRequest): Promise<AsyncIterable<StreamChunk>> {
    const validated = ChatRequestSchema.parse({ ...request, stream: true });
    
    await this.rateLimiter.acquire(this.estimateTokens(validated));
    
    const response = await fetch(`${this.baseUrl}/chat/completions`, {
      method: 'POST',
      headers: {
        'Authorization': `Bearer ${this.apiKey}`,
        'Content-Type': 'application/json'
      },
      body: JSON.stringify(validated)
    });
    
    // Extract balance even for streaming
    this.extractBalance(response.headers);
    this.extractRateLimits(response.headers);
    
    if (!response.ok) {
      throw await this.handleError(response);
    }
    
    return this.parseSSEStream(response.body!);
  }
  
  // Extract balance from EVERY response
  private extractBalance(headers: Headers): void {
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
  }
  
  private extractRateLimits(headers: Headers): void {
    this.rateLimiter.updateLimits(headers);
  }
  
  private async handleError(response: Response): Promise<VeniceApiError> {
    let body: any = {};
    try {
      body = await response.json();
    } catch {
      // Response might not be JSON
    }
    
    const error = new VeniceApiError(
      response.status,
      body.error?.type ?? 'unknown_error',
      body.error?.message ?? `HTTP ${response.status}`
    );
    
    if (response.status === 429) {
      error.isRateLimited = true;
      error.retryAfter = parseInt(response.headers.get('Retry-After') ?? '30');
    }
    
    return error;
  }
  
  private estimateTokens(request: ChatRequest): number {
    // Rough estimate: 4 chars ≈ 1 token
    const messageChars = request.messages
      .reduce((sum, m) => sum + m.content.length, 0);
    return Math.ceil(messageChars / 4) + (request.max_tokens ?? 1000);
  }
  
  private async *parseSSEStream(body: ReadableStream<Uint8Array>): AsyncIterable<StreamChunk> {
    const reader = body.getReader();
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
          
          try {
            yield JSON.parse(data);
          } catch {
            // Ignore malformed chunks
          }
        }
      }
    }
  }
}
```

### Error Types

```typescript
// bridge/src/venice/errors.ts

export class VeniceApiError extends Error {
  readonly statusCode: number;
  readonly errorType: string;
  isRateLimited = false;
  retryAfter?: number;
  
  constructor(statusCode: number, errorType: string, message: string) {
    super(message);
    this.name = 'VeniceApiError';
    this.statusCode = statusCode;
    this.errorType = errorType;
  }
  
  toJSON() {
    return {
      code: this.getErrorCode(),
      message: this.message,
      type: this.errorType,
      retryAfter: this.retryAfter
    };
  }
  
  private getErrorCode(): number {
    switch (this.statusCode) {
      case 401: return 2001;  // AUTH_INVALID_KEY
      case 403: return 2002;  // AUTH_FORBIDDEN
      case 429: return 3001;  // RATE_LIMIT_EXCEEDED
      case 500: return 9001;  // INTERNAL_ERROR
      default: return 1000;   // NETWORK_ERROR
    }
  }
}
```

---

## API Key Management

### Secure Storage

```typescript
// bridge/src/venice/keychain.ts
import keytar from 'keytar';

const SERVICE_NAME = 'opencode-sidepanel';
const ACCOUNT_NAME = 'venice-api-key';

export async function getApiKey(): Promise<string | null> {
  return keytar.getPassword(SERVICE_NAME, ACCOUNT_NAME);
}

export async function setApiKey(key: string): Promise<void> {
  await keytar.setPassword(SERVICE_NAME, ACCOUNT_NAME, key);
}

export async function deleteApiKey(): Promise<boolean> {
  return keytar.deletePassword(SERVICE_NAME, ACCOUNT_NAME);
}

// Validate key format
export function validateApiKey(key: string): boolean {
  // Venice keys start with 'vk_'
  return /^vk_[a-zA-Z0-9]{32,}$/.test(key);
}
```

### Key Loading

```typescript
// bridge/src/venice/config.ts

export async function loadVeniceConfig(): Promise<VeniceConfig> {
  // 1. Try keychain
  let apiKey = await getApiKey();
  
  // 2. Fall back to environment variable
  if (!apiKey) {
    apiKey = process.env.VENICE_API_KEY ?? null;
  }
  
  // 3. Fall back to file
  if (!apiKey) {
    const keyFile = process.env.VENICE_API_KEY_FILE;
    if (keyFile && fs.existsSync(keyFile)) {
      apiKey = fs.readFileSync(keyFile, 'utf-8').trim();
    }
  }
  
  if (!apiKey) {
    throw new Error('Venice API key not found. Run `just store-api-key` to configure.');
  }
  
  if (!validateApiKey(apiKey)) {
    throw new Error('Invalid Venice API key format');
  }
  
  return {
    apiKey,
    baseUrl: process.env.VENICE_API_URL ?? 'https://api.venice.ai/api/v1'
  };
}
```

---

## Request Queuing

```typescript
// bridge/src/venice/queue.ts

interface QueuedRequest<T> {
  execute: () => Promise<T>;
  resolve: (value: T) => void;
  reject: (error: Error) => void;
  priority: number;
  enqueuedAt: Date;
}

export class RequestQueue {
  private queue: QueuedRequest<any>[] = [];
  private processing = false;
  private maxConcurrent = 3;
  private activeCount = 0;
  
  async enqueue<T>(
    execute: () => Promise<T>,
    priority: number = 0
  ): Promise<T> {
    return new Promise((resolve, reject) => {
      const request: QueuedRequest<T> = {
        execute,
        resolve,
        reject,
        priority,
        enqueuedAt: new Date()
      };
      
      // Insert by priority (higher = sooner)
      const insertIdx = this.queue.findIndex(r => r.priority < priority);
      if (insertIdx === -1) {
        this.queue.push(request);
      } else {
        this.queue.splice(insertIdx, 0, request);
      }
      
      this.processQueue();
    });
  }
  
  private async processQueue(): Promise<void> {
    if (this.processing) return;
    this.processing = true;
    
    while (this.queue.length > 0 && this.activeCount < this.maxConcurrent) {
      const request = this.queue.shift()!;
      this.activeCount++;
      
      this.executeRequest(request).finally(() => {
        this.activeCount--;
        this.processQueue();
      });
    }
    
    this.processing = false;
  }
  
  private async executeRequest<T>(request: QueuedRequest<T>): Promise<void> {
    try {
      const result = await request.execute();
      request.resolve(result);
    } catch (error) {
      request.reject(error as Error);
    }
  }
  
  // Queue status for monitoring
  getStatus(): QueueStatus {
    return {
      queueLength: this.queue.length,
      activeRequests: this.activeCount,
      oldestWaitMs: this.queue.length > 0
        ? Date.now() - this.queue[0].enqueuedAt.getTime()
        : 0
    };
  }
}
```

---

## Retry Logic

```typescript
// bridge/src/venice/retry.ts

interface RetryConfig {
  maxRetries: number;
  baseDelayMs: number;
  maxDelayMs: number;
  retryableErrors: number[];
}

const defaultConfig: RetryConfig = {
  maxRetries: 3,
  baseDelayMs: 1000,
  maxDelayMs: 30000,
  retryableErrors: [429, 500, 502, 503, 504]
};

export async function withRetry<T>(
  operation: () => Promise<T>,
  config: Partial<RetryConfig> = {}
): Promise<T> {
  const { maxRetries, baseDelayMs, maxDelayMs, retryableErrors } = {
    ...defaultConfig,
    ...config
  };
  
  let lastError: Error | undefined;
  
  for (let attempt = 0; attempt <= maxRetries; attempt++) {
    try {
      return await operation();
    } catch (error) {
      lastError = error as Error;
      
      // Check if retryable
      if (error instanceof VeniceApiError) {
        if (!retryableErrors.includes(error.statusCode)) {
          throw error;  // Not retryable
        }
        
        // Use Retry-After header if available
        if (error.retryAfter) {
          await delay(error.retryAfter * 1000);
          continue;
        }
      }
      
      // Exponential backoff with jitter
      if (attempt < maxRetries) {
        const delayMs = Math.min(
          baseDelayMs * Math.pow(2, attempt) + Math.random() * 1000,
          maxDelayMs
        );
        await delay(delayMs);
      }
    }
  }
  
  throw lastError;
}

function delay(ms: number): Promise<void> {
  return new Promise(resolve => setTimeout(resolve, ms));
}
```

---

## Usage Example

```typescript
// In bridge server
const veniceClient = new VeniceClient(config, store);

// Handle chat request from browser
app.post('/api/chat', async (req, res) => {
  try {
    const response = await veniceClient.chat(req.body);
    res.json(response);
  } catch (error) {
    if (error instanceof VeniceApiError) {
      res.status(error.statusCode).json(error.toJSON());
    } else {
      res.status(500).json({ error: 'Internal server error' });
    }
  }
});

// Streaming
app.post('/api/chat/stream', async (req, res) => {
  res.setHeader('Content-Type', 'text/event-stream');
  res.setHeader('Cache-Control', 'no-cache');
  
  try {
    const stream = await veniceClient.streamChat(req.body);
    
    for await (const chunk of stream) {
      res.write(`data: ${JSON.stringify(chunk)}\n\n`);
    }
    
    res.write('data: [DONE]\n\n');
    res.end();
  } catch (error) {
    res.write(`data: ${JSON.stringify({ error: error.message })}\n\n`);
    res.end();
  }
});
```

---

## Related Specifications

- `10-VENICE-API-OVERVIEW.md` - API details
- `11-DIEM-TRACKING.md` - Balance tracking
- `14-RATE-LIMIT-HANDLING.md` - Rate limits
- `83-SECURITY-MODEL.md` - Key security

---

*"The proxy is invisible when it works perfectly."*
