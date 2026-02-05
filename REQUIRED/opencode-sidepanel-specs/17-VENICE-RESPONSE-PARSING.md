# 17-VENICE-RESPONSE-PARSING: Extracting Data from API Responses

## Overview

Venice API responses contain critical metadata in headers and structured data in the body. This document specifies how to parse, validate, and extract information from Venice responses.

---

## Response Structure

### Headers

```http
HTTP/1.1 200 OK
Content-Type: application/json
x-venice-balance-diem: 42.5
x-venice-balance-usd: 12.34
x-venice-model: llama-3.3-70b
x-venice-request-id: req_abc123
x-ratelimit-limit: 100
x-ratelimit-remaining: 95
x-ratelimit-reset: 1705312800
```

### Body (Streaming)

```
data: {"id":"chatcmpl-123","object":"chat.completion.chunk","created":1705312345,"model":"llama-3.3-70b","choices":[{"index":0,"delta":{"content":"Hello"},"finish_reason":null}]}

data: {"id":"chatcmpl-123","object":"chat.completion.chunk","created":1705312345,"model":"llama-3.3-70b","choices":[{"index":0,"delta":{"content":" world"},"finish_reason":null}]}

data: {"id":"chatcmpl-123","object":"chat.completion.chunk","created":1705312345,"model":"llama-3.3-70b","choices":[{"index":0,"delta":{},"finish_reason":"stop"}],"usage":{"prompt_tokens":10,"completion_tokens":2,"total_tokens":12}}

data: [DONE]
```

### Body (Non-Streaming)

```json
{
  "id": "chatcmpl-123",
  "object": "chat.completion",
  "created": 1705312345,
  "model": "llama-3.3-70b",
  "choices": [
    {
      "index": 0,
      "message": {
        "role": "assistant",
        "content": "Hello world"
      },
      "finish_reason": "stop"
    }
  ],
  "usage": {
    "prompt_tokens": 10,
    "completion_tokens": 2,
    "total_tokens": 12
  }
}
```

---

## Data Model

```typescript
interface VeniceResponse {
  // From headers
  headers: VeniceHeaders;
  
  // From body
  body: ChatCompletion | ChatCompletionChunk;
}

interface VeniceHeaders {
  // Balance (CRITICAL)
  balanceDiem: number;
  balanceUsd: number;
  
  // Model info
  model: string;
  requestId: string;
  
  // Rate limits
  rateLimit: {
    limit: number;
    remaining: number;
    resetTimestamp: number;
  };
}

interface ChatCompletion {
  id: string;
  object: 'chat.completion';
  created: number;
  model: string;
  choices: Choice[];
  usage: Usage;
}

interface ChatCompletionChunk {
  id: string;
  object: 'chat.completion.chunk';
  created: number;
  model: string;
  choices: ChunkChoice[];
  usage?: Usage;  // Only on final chunk
}

interface Choice {
  index: number;
  message: {
    role: 'assistant';
    content: string;
    tool_calls?: ToolCall[];
  };
  finish_reason: FinishReason;
}

interface ChunkChoice {
  index: number;
  delta: {
    role?: 'assistant';
    content?: string;
    tool_calls?: ToolCallDelta[];
  };
  finish_reason: FinishReason | null;
}

interface Usage {
  prompt_tokens: number;
  completion_tokens: number;
  total_tokens: number;
}

type FinishReason = 'stop' | 'length' | 'tool_calls' | 'content_filter';
```

---

## Header Parsing

```typescript
// bridge/src/venice/headers.ts

export function parseVeniceHeaders(headers: Headers): VeniceHeaders {
  return {
    // Balance - CRITICAL, must always extract
    balanceDiem: parseFloat(headers.get('x-venice-balance-diem') ?? '0'),
    balanceUsd: parseFloat(headers.get('x-venice-balance-usd') ?? '0'),
    
    // Model info
    model: headers.get('x-venice-model') ?? 'unknown',
    requestId: headers.get('x-venice-request-id') ?? '',
    
    // Rate limits
    rateLimit: {
      limit: parseInt(headers.get('x-ratelimit-limit') ?? '100', 10),
      remaining: parseInt(headers.get('x-ratelimit-remaining') ?? '100', 10),
      resetTimestamp: parseInt(headers.get('x-ratelimit-reset') ?? '0', 10)
    }
  };
}

// Validate headers are present
export function validateVeniceHeaders(headers: VeniceHeaders): ValidationResult {
  const errors: string[] = [];
  
  if (isNaN(headers.balanceDiem)) {
    errors.push('Missing or invalid x-venice-balance-diem header');
  }
  
  if (isNaN(headers.balanceUsd)) {
    errors.push('Missing or invalid x-venice-balance-usd header');
  }
  
  if (!headers.requestId) {
    errors.push('Missing x-venice-request-id header');
  }
  
  return {
    valid: errors.length === 0,
    errors
  };
}
```

---

## Streaming Response Parsing

```typescript
// bridge/src/venice/streaming.ts

export async function* parseSSEStream(
  response: Response
): AsyncGenerator<ChatCompletionChunk | 'DONE'> {
  const reader = response.body!.getReader();
  const decoder = new TextDecoder();
  let buffer = '';
  
  try {
    while (true) {
      const { done, value } = await reader.read();
      if (done) break;
      
      buffer += decoder.decode(value, { stream: true });
      const lines = buffer.split('\n');
      buffer = lines.pop() ?? '';
      
      for (const line of lines) {
        if (line.startsWith('data: ')) {
          const data = line.slice(6).trim();
          
          if (data === '[DONE]') {
            yield 'DONE';
            return;
          }
          
          try {
            const chunk = JSON.parse(data) as ChatCompletionChunk;
            yield chunk;
          } catch (e) {
            console.error('Failed to parse SSE chunk:', data, e);
          }
        }
      }
    }
  } finally {
    reader.releaseLock();
  }
}

// Accumulate streaming response
export class StreamAccumulator {
  private content: string = '';
  private toolCalls: Map<number, ToolCall> = new Map();
  private usage: Usage | null = null;
  private finishReason: FinishReason | null = null;
  
  addChunk(chunk: ChatCompletionChunk): void {
    const choice = chunk.choices[0];
    if (!choice) return;
    
    // Accumulate content
    if (choice.delta.content) {
      this.content += choice.delta.content;
    }
    
    // Accumulate tool calls
    if (choice.delta.tool_calls) {
      for (const tc of choice.delta.tool_calls) {
        const existing = this.toolCalls.get(tc.index);
        if (existing) {
          // Append to existing
          existing.function.arguments += tc.function?.arguments ?? '';
        } else {
          // New tool call
          this.toolCalls.set(tc.index, {
            id: tc.id!,
            type: 'function',
            function: {
              name: tc.function!.name!,
              arguments: tc.function?.arguments ?? ''
            }
          });
        }
      }
    }
    
    // Capture finish reason
    if (choice.finish_reason) {
      this.finishReason = choice.finish_reason;
    }
    
    // Capture usage (only on final chunk)
    if (chunk.usage) {
      this.usage = chunk.usage;
    }
  }
  
  getResult(): StreamResult {
    return {
      content: this.content,
      toolCalls: Array.from(this.toolCalls.values()),
      usage: this.usage,
      finishReason: this.finishReason
    };
  }
}
```

---

## Response Validation

```typescript
// bridge/src/venice/validation.ts

import Ajv from 'ajv';

const ajv = new Ajv();

// JSON Schema for chat completion
const chatCompletionSchema = {
  type: 'object',
  required: ['id', 'object', 'created', 'model', 'choices'],
  properties: {
    id: { type: 'string' },
    object: { enum: ['chat.completion', 'chat.completion.chunk'] },
    created: { type: 'number' },
    model: { type: 'string' },
    choices: {
      type: 'array',
      items: {
        type: 'object',
        required: ['index'],
        properties: {
          index: { type: 'number' },
          message: {
            type: 'object',
            properties: {
              role: { type: 'string' },
              content: { type: 'string' }
            }
          },
          delta: {
            type: 'object',
            properties: {
              role: { type: 'string' },
              content: { type: 'string' }
            }
          },
          finish_reason: { 
            enum: ['stop', 'length', 'tool_calls', 'content_filter', null] 
          }
        }
      }
    },
    usage: {
      type: 'object',
      properties: {
        prompt_tokens: { type: 'number' },
        completion_tokens: { type: 'number' },
        total_tokens: { type: 'number' }
      }
    }
  }
};

const validateChatCompletion = ajv.compile(chatCompletionSchema);

export function validateResponse(data: unknown): ValidationResult {
  const valid = validateChatCompletion(data);
  
  if (!valid) {
    return {
      valid: false,
      errors: validateChatCompletion.errors?.map(e => e.message ?? 'Unknown error') ?? []
    };
  }
  
  return { valid: true, errors: [] };
}
```

---

## Error Response Parsing

```typescript
interface VeniceError {
  error: {
    message: string;
    type: string;
    code: string;
    param?: string;
  };
}

export function parseErrorResponse(response: Response, body: unknown): ParsedError {
  // Try to parse as Venice error
  if (isVeniceError(body)) {
    return {
      code: body.error.code,
      message: body.error.message,
      type: body.error.type,
      status: response.status,
      retryable: isRetryable(response.status, body.error.code)
    };
  }
  
  // Fallback for unexpected errors
  return {
    code: 'UNKNOWN_ERROR',
    message: String(body),
    type: 'unknown',
    status: response.status,
    retryable: response.status >= 500
  };
}

function isRetryable(status: number, code: string): boolean {
  // Server errors are retryable
  if (status >= 500) return true;
  
  // Rate limits are retryable after delay
  if (status === 429) return true;
  
  // Specific retryable codes
  if (code === 'overloaded' || code === 'timeout') return true;
  
  return false;
}
```

---

## PureScript Types

```purescript
module Sidepanel.Venice.Response where

type VeniceHeaders =
  { balanceDiem :: Number
  , balanceUsd :: Number
  , model :: String
  , requestId :: String
  , rateLimit :: RateLimit
  }

type RateLimit =
  { limit :: Int
  , remaining :: Int
  , resetTimestamp :: Int
  }

type Usage =
  { promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  }

type ChatCompletion =
  { id :: String
  , model :: String
  , choices :: Array Choice
  , usage :: Usage
  }

type Choice =
  { index :: Int
  , message :: Message
  , finishReason :: FinishReason
  }

data FinishReason
  = Stop
  | Length
  | ToolCalls
  | ContentFilter

derive instance eqFinishReason :: Eq FinishReason
```

---

## Related Specifications

- `10-VENICE-API-OVERVIEW.md` - API structure
- `11-DIEM-TRACKING.md` - Balance extraction
- `14-RATE-LIMIT-HANDLING.md` - Rate limit handling

---

*"Parse every response. Miss no detail."*
