# 18-VENICE-ERROR-HANDLING: Error Codes and Recovery Strategies

## Overview

This document specifies how to handle errors from the Venice API, including error categorization, user messaging, and recovery strategies.

---

## Error Categories

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          VENICE ERROR TAXONOMY                              │
│                                                                              │
│  ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐             │
│  │   RETRYABLE     │  │   RECOVERABLE   │  │    TERMINAL     │             │
│  │                 │  │                 │  │                 │             │
│  │  • Rate limits  │  │  • Invalid req  │  │  • Auth failed  │             │
│  │  • Timeouts     │  │  • Bad params   │  │  • Account ban  │             │
│  │  • Server 5xx   │  │  • Model busy   │  │  • API disabled │             │
│  │  • Network err  │  │  • Context len  │  │                 │             │
│  │                 │  │                 │  │                 │             │
│  │  Action: Retry  │  │  Action: Fix    │  │  Action: Stop   │             │
│  │  with backoff   │  │  and retry      │  │  and alert      │             │
│  └─────────────────┘  └─────────────────┘  └─────────────────┘             │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Error Code Reference

### HTTP Status Codes

| Status | Meaning | Category | Action |
|--------|---------|----------|--------|
| 400 | Bad Request | Recoverable | Fix request |
| 401 | Unauthorized | Terminal | Check API key |
| 403 | Forbidden | Terminal | Check permissions |
| 404 | Not Found | Recoverable | Check endpoint |
| 408 | Request Timeout | Retryable | Retry with backoff |
| 413 | Payload Too Large | Recoverable | Reduce context |
| 429 | Too Many Requests | Retryable | Wait and retry |
| 500 | Internal Server Error | Retryable | Retry with backoff |
| 502 | Bad Gateway | Retryable | Retry with backoff |
| 503 | Service Unavailable | Retryable | Retry with backoff |
| 504 | Gateway Timeout | Retryable | Retry with backoff |

### Venice Error Codes

| Code | Description | Category | User Message |
|------|-------------|----------|--------------|
| `invalid_api_key` | API key invalid | Terminal | "API key is invalid. Please check settings." |
| `insufficient_quota` | Balance depleted | Terminal | "Balance depleted. Wait for daily reset." |
| `rate_limit_exceeded` | Too many requests | Retryable | "Rate limit hit. Retrying in {n} seconds..." |
| `model_not_found` | Model unavailable | Recoverable | "Model unavailable. Switching to default." |
| `context_length_exceeded` | Input too long | Recoverable | "Message too long. Reducing context..." |
| `content_filter` | Content blocked | Recoverable | "Content blocked by safety filter." |
| `server_error` | Internal error | Retryable | "Server error. Retrying..." |
| `timeout` | Request timeout | Retryable | "Request timed out. Retrying..." |
| `overloaded` | Service busy | Retryable | "Service busy. Retrying in {n} seconds..." |

---

## Data Model

```typescript
interface VeniceError {
  // Error identification
  code: VeniceErrorCode;
  status: number;
  message: string;
  
  // Categorization
  category: ErrorCategory;
  retryable: boolean;
  
  // Recovery info
  retryAfter?: number;      // Seconds to wait
  suggestion?: string;      // How to fix
  
  // Context
  requestId?: string;
  model?: string;
  timestamp: Date;
}

type ErrorCategory = 'retryable' | 'recoverable' | 'terminal';

type VeniceErrorCode =
  | 'invalid_api_key'
  | 'insufficient_quota'
  | 'rate_limit_exceeded'
  | 'model_not_found'
  | 'context_length_exceeded'
  | 'content_filter'
  | 'server_error'
  | 'timeout'
  | 'overloaded'
  | 'network_error'
  | 'unknown';

interface RetryConfig {
  maxAttempts: number;
  initialDelay: number;
  maxDelay: number;
  backoffMultiplier: number;
}
```

---

## Error Handler Implementation

```typescript
// bridge/src/venice/errors.ts

export class VeniceErrorHandler {
  private retryConfig: RetryConfig = {
    maxAttempts: 3,
    initialDelay: 1000,
    maxDelay: 30000,
    backoffMultiplier: 2
  };
  
  async handleError(
    error: VeniceError,
    request: () => Promise<Response>,
    attempt: number = 1
  ): Promise<Response | VeniceError> {
    
    // Log error
    this.logError(error, attempt);
    
    // Categorize and handle
    switch (error.category) {
      case 'retryable':
        return this.handleRetryable(error, request, attempt);
      
      case 'recoverable':
        return this.handleRecoverable(error);
      
      case 'terminal':
        return this.handleTerminal(error);
    }
  }
  
  private async handleRetryable(
    error: VeniceError,
    request: () => Promise<Response>,
    attempt: number
  ): Promise<Response | VeniceError> {
    
    if (attempt >= this.retryConfig.maxAttempts) {
      return {
        ...error,
        message: `Failed after ${attempt} attempts: ${error.message}`
      };
    }
    
    // Calculate delay
    const delay = this.calculateDelay(error, attempt);
    
    // Notify UI
    this.notifyRetry(error, delay, attempt);
    
    // Wait
    await this.sleep(delay);
    
    // Retry
    try {
      return await request();
    } catch (retryError) {
      return this.handleError(
        this.parseError(retryError),
        request,
        attempt + 1
      );
    }
  }
  
  private calculateDelay(error: VeniceError, attempt: number): number {
    // Use server-provided retry-after if available
    if (error.retryAfter) {
      return error.retryAfter * 1000;
    }
    
    // Exponential backoff with jitter
    const exponential = this.retryConfig.initialDelay *
      Math.pow(this.retryConfig.backoffMultiplier, attempt - 1);
    
    const capped = Math.min(exponential, this.retryConfig.maxDelay);
    
    // Add ±20% jitter
    const jitter = capped * 0.2 * (Math.random() * 2 - 1);
    
    return Math.round(capped + jitter);
  }
  
  private handleRecoverable(error: VeniceError): VeniceError {
    // Provide recovery suggestions
    switch (error.code) {
      case 'context_length_exceeded':
        return {
          ...error,
          suggestion: 'Try removing some files from context or starting a new session.'
        };
      
      case 'model_not_found':
        return {
          ...error,
          suggestion: 'The selected model is unavailable. Switch to a different model.'
        };
      
      case 'content_filter':
        return {
          ...error,
          suggestion: 'Your message was blocked by the safety filter. Please rephrase.'
        };
      
      default:
        return error;
    }
  }
  
  private handleTerminal(error: VeniceError): VeniceError {
    // Terminal errors require user action
    switch (error.code) {
      case 'invalid_api_key':
        return {
          ...error,
          suggestion: 'Please check your Venice API key in settings.'
        };
      
      case 'insufficient_quota':
        return {
          ...error,
          suggestion: `Balance depleted. Resets at midnight UTC (${this.getTimeToReset()}).`
        };
      
      default:
        return error;
    }
  }
  
  parseError(error: unknown): VeniceError {
    // Network error
    if (error instanceof TypeError && error.message.includes('fetch')) {
      return {
        code: 'network_error',
        status: 0,
        message: 'Network connection failed',
        category: 'retryable',
        retryable: true,
        timestamp: new Date()
      };
    }
    
    // Response error
    if (error instanceof Response) {
      return this.parseResponseError(error);
    }
    
    // Unknown error
    return {
      code: 'unknown',
      status: 0,
      message: String(error),
      category: 'retryable',
      retryable: true,
      timestamp: new Date()
    };
  }
  
  private notifyRetry(error: VeniceError, delay: number, attempt: number): void {
    this.wsManager.broadcast({
      jsonrpc: '2.0',
      method: 'error.retry',
      params: {
        code: error.code,
        message: error.message,
        delay,
        attempt,
        maxAttempts: this.retryConfig.maxAttempts
      }
    });
  }
}
```

---

## User-Facing Messages

### Toast Notifications

```typescript
const ERROR_MESSAGES: Record<VeniceErrorCode, ErrorMessage> = {
  rate_limit_exceeded: {
    title: 'Rate Limit',
    message: 'Too many requests. Retrying in {delay}s...',
    level: 'warning'
  },
  server_error: {
    title: 'Server Error',
    message: 'Venice is having issues. Retrying...',
    level: 'warning'
  },
  timeout: {
    title: 'Timeout',
    message: 'Request timed out. Retrying...',
    level: 'warning'
  },
  insufficient_quota: {
    title: 'Balance Depleted',
    message: 'No Diem remaining. Resets at midnight UTC.',
    level: 'error'
  },
  invalid_api_key: {
    title: 'Authentication Failed',
    message: 'Invalid API key. Check settings.',
    level: 'error'
  },
  context_length_exceeded: {
    title: 'Context Too Long',
    message: 'Remove some files from context.',
    level: 'warning'
  },
  content_filter: {
    title: 'Content Blocked',
    message: 'Message blocked by safety filter.',
    level: 'warning'
  },
  network_error: {
    title: 'Connection Lost',
    message: 'Network error. Check your connection.',
    level: 'error'
  }
};
```

### Error Display Component

```purescript
renderError :: VeniceError -> H.ComponentHTML Action () m
renderError error =
  HH.div
    [ HP.classes $ errorClasses error.category ]
    [ HH.div [ HP.class_ (H.ClassName "error-header") ]
        [ HH.span [ HP.class_ (H.ClassName "error-icon") ]
            [ HH.text $ errorIcon error.category ]
        , HH.span [ HP.class_ (H.ClassName "error-title") ]
            [ HH.text $ errorTitle error.code ]
        ]
    , HH.div [ HP.class_ (H.ClassName "error-message") ]
        [ HH.text error.message ]
    , case error.suggestion of
        Just suggestion ->
          HH.div [ HP.class_ (H.ClassName "error-suggestion") ]
            [ HH.text suggestion ]
        Nothing -> HH.text ""
    , when error.retryable $
        HH.div [ HP.class_ (H.ClassName "error-retry") ]
            [ HH.text $ "Retrying in " <> show (fromMaybe 0 error.retryAfter) <> "s..." ]
    ]
```

---

## Recovery Strategies

### Context Length Recovery

```typescript
async function recoverFromContextLength(
  request: ChatRequest,
  maxTokens: number
): Promise<ChatRequest> {
  // Strategy 1: Remove oldest messages
  const reducedMessages = request.messages.slice(-10);
  
  // Strategy 2: Summarize old context
  if (estimateTokens(reducedMessages) > maxTokens) {
    const summary = await summarizeContext(request.messages.slice(0, -5));
    return {
      ...request,
      messages: [
        { role: 'system', content: `Previous context summary: ${summary}` },
        ...request.messages.slice(-5)
      ]
    };
  }
  
  return { ...request, messages: reducedMessages };
}
```

### Model Fallback

```typescript
const MODEL_FALLBACKS: Record<string, string[]> = {
  'llama-3.1-405b': ['llama-3.3-70b', 'qwen-2.5-72b'],
  'llama-3.3-70b': ['qwen-2.5-72b', 'deepseek-r1-70b'],
  'qwen-2.5-72b': ['llama-3.3-70b', 'deepseek-r1-70b']
};

async function tryWithFallback(
  request: ChatRequest,
  error: VeniceError
): Promise<Response> {
  if (error.code !== 'model_not_found') {
    throw error;
  }
  
  const fallbacks = MODEL_FALLBACKS[request.model] ?? [];
  
  for (const fallback of fallbacks) {
    try {
      notifyModelSwitch(request.model, fallback);
      return await makeRequest({ ...request, model: fallback });
    } catch (e) {
      continue;
    }
  }
  
  throw error;
}
```

---

## CSS Styling

```css
.error-display {
  padding: var(--space-3);
  border-radius: 8px;
  margin: var(--space-2) 0;
}

.error-display--retryable {
  background: var(--color-warning-dim);
  border-left: 4px solid var(--color-warning);
}

.error-display--recoverable {
  background: var(--color-info-dim);
  border-left: 4px solid var(--color-info);
}

.error-display--terminal {
  background: var(--color-error-dim);
  border-left: 4px solid var(--color-error);
}

.error-header {
  display: flex;
  align-items: center;
  gap: var(--space-2);
  margin-bottom: var(--space-2);
}

.error-title {
  font-weight: var(--font-weight-semibold);
}

.error-message {
  color: var(--color-text-secondary);
  margin-bottom: var(--space-2);
}

.error-suggestion {
  font-size: var(--font-size-sm);
  color: var(--color-text-tertiary);
  font-style: italic;
}

.error-retry {
  font-size: var(--font-size-sm);
  color: var(--color-warning);
  margin-top: var(--space-2);
}
```

---

## Related Specifications

- `17-VENICE-RESPONSE-PARSING.md` - Response parsing
- `14-RATE-LIMIT-HANDLING.md` - Rate limits
- `80-ERROR-TAXONOMY.md` - Error codes

---

*"Errors are inevitable. How you handle them defines the experience."*
