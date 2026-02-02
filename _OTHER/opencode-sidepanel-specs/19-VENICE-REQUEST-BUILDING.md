# 19-VENICE-REQUEST-BUILDING: Constructing API Requests

## Overview

This document specifies how to build requests for the Venice API, including message formatting, tool definitions, and streaming configuration.

---

## Request Structure

### Chat Completion Request

```typescript
interface ChatRequest {
  // Required
  model: string;
  messages: Message[];
  
  // Optional
  temperature?: number;         // 0-2, default 1
  top_p?: number;              // 0-1, default 1
  max_tokens?: number;         // Max output tokens
  stream?: boolean;            // Enable streaming
  stop?: string | string[];    // Stop sequences
  
  // Tools
  tools?: Tool[];
  tool_choice?: ToolChoice;
  
  // Advanced
  presence_penalty?: number;   // -2 to 2
  frequency_penalty?: number;  // -2 to 2
  user?: string;               // User identifier
}

interface Message {
  role: 'system' | 'user' | 'assistant' | 'tool';
  content: string | ContentPart[];
  name?: string;               // For tool messages
  tool_call_id?: string;       // For tool responses
  tool_calls?: ToolCall[];     // For assistant tool calls
}

interface ContentPart {
  type: 'text' | 'image_url';
  text?: string;
  image_url?: {
    url: string;
    detail?: 'low' | 'high' | 'auto';
  };
}
```

---

## Request Builder

```typescript
// bridge/src/venice/request.ts

export class VeniceRequestBuilder {
  private request: Partial<ChatRequest> = {};
  
  model(model: string): this {
    this.request.model = model;
    return this;
  }
  
  messages(messages: Message[]): this {
    this.request.messages = messages;
    return this;
  }
  
  addMessage(role: Message['role'], content: string): this {
    this.request.messages = this.request.messages ?? [];
    this.request.messages.push({ role, content });
    return this;
  }
  
  system(content: string): this {
    return this.addMessage('system', content);
  }
  
  user(content: string): this {
    return this.addMessage('user', content);
  }
  
  assistant(content: string): this {
    return this.addMessage('assistant', content);
  }
  
  temperature(value: number): this {
    this.request.temperature = Math.max(0, Math.min(2, value));
    return this;
  }
  
  maxTokens(value: number): this {
    this.request.max_tokens = value;
    return this;
  }
  
  stream(enabled: boolean = true): this {
    this.request.stream = enabled;
    return this;
  }
  
  tools(tools: Tool[]): this {
    this.request.tools = tools;
    return this;
  }
  
  toolChoice(choice: ToolChoice): this {
    this.request.tool_choice = choice;
    return this;
  }
  
  stop(sequences: string | string[]): this {
    this.request.stop = sequences;
    return this;
  }
  
  build(): ChatRequest {
    if (!this.request.model) {
      throw new Error('Model is required');
    }
    if (!this.request.messages?.length) {
      throw new Error('At least one message is required');
    }
    
    return this.request as ChatRequest;
  }
  
  // Convenience method for full request
  static create(
    model: string,
    messages: Message[],
    options?: Partial<ChatRequest>
  ): ChatRequest {
    return {
      model,
      messages,
      stream: true,  // Default to streaming
      ...options
    };
  }
}

// Usage
const request = new VeniceRequestBuilder()
  .model('llama-3.3-70b')
  .system('You are a helpful coding assistant.')
  .user('Help me debug this function')
  .temperature(0.7)
  .maxTokens(4096)
  .stream()
  .build();
```

---

## Tool Definitions

```typescript
interface Tool {
  type: 'function';
  function: FunctionDefinition;
}

interface FunctionDefinition {
  name: string;
  description: string;
  parameters: JSONSchema;
}

type ToolChoice = 
  | 'none'           // Don't use tools
  | 'auto'           // Model decides
  | 'required'       // Must use a tool
  | { type: 'function'; function: { name: string } };  // Specific tool

// Common tools for coding
const CODING_TOOLS: Tool[] = [
  {
    type: 'function',
    function: {
      name: 'read_file',
      description: 'Read the contents of a file',
      parameters: {
        type: 'object',
        properties: {
          path: {
            type: 'string',
            description: 'Path to the file'
          }
        },
        required: ['path']
      }
    }
  },
  {
    type: 'function',
    function: {
      name: 'write_file',
      description: 'Write content to a file',
      parameters: {
        type: 'object',
        properties: {
          path: {
            type: 'string',
            description: 'Path to the file'
          },
          content: {
            type: 'string',
            description: 'Content to write'
          }
        },
        required: ['path', 'content']
      }
    }
  },
  {
    type: 'function',
    function: {
      name: 'run_command',
      description: 'Run a shell command',
      parameters: {
        type: 'object',
        properties: {
          command: {
            type: 'string',
            description: 'Command to execute'
          }
        },
        required: ['command']
      }
    }
  }
];
```

---

## Message Formatting

### Text Messages

```typescript
function formatUserMessage(content: string): Message {
  return {
    role: 'user',
    content
  };
}

function formatAssistantMessage(
  content: string,
  toolCalls?: ToolCall[]
): Message {
  const message: Message = {
    role: 'assistant',
    content
  };
  
  if (toolCalls?.length) {
    message.tool_calls = toolCalls;
  }
  
  return message;
}
```

### Tool Messages

```typescript
function formatToolResult(
  toolCallId: string,
  result: unknown
): Message {
  return {
    role: 'tool',
    tool_call_id: toolCallId,
    content: typeof result === 'string' 
      ? result 
      : JSON.stringify(result)
  };
}

// Complete tool call cycle
function buildToolCallMessages(
  assistantMessage: Message,
  toolResults: Map<string, unknown>
): Message[] {
  const messages: Message[] = [assistantMessage];
  
  for (const toolCall of assistantMessage.tool_calls ?? []) {
    const result = toolResults.get(toolCall.id);
    messages.push(formatToolResult(toolCall.id, result));
  }
  
  return messages;
}
```

### Context Building

```typescript
interface ContextConfig {
  maxTokens: number;
  reserveForOutput: number;
  includeSystemPrompt: boolean;
}

function buildContext(
  systemPrompt: string,
  history: Message[],
  fileContext: FileContext[],
  config: ContextConfig
): Message[] {
  const messages: Message[] = [];
  let tokenCount = 0;
  const maxInput = config.maxTokens - config.reserveForOutput;
  
  // System prompt first
  if (config.includeSystemPrompt && systemPrompt) {
    const systemTokens = estimateTokens(systemPrompt);
    if (tokenCount + systemTokens <= maxInput) {
      messages.push({ role: 'system', content: systemPrompt });
      tokenCount += systemTokens;
    }
  }
  
  // File context
  for (const file of fileContext) {
    const fileContent = formatFileContext(file);
    const fileTokens = estimateTokens(fileContent);
    
    if (tokenCount + fileTokens <= maxInput) {
      messages.push({ role: 'system', content: fileContent });
      tokenCount += fileTokens;
    } else {
      break;  // Stop adding files
    }
  }
  
  // History (most recent first, then reverse)
  const historyToInclude: Message[] = [];
  for (let i = history.length - 1; i >= 0; i--) {
    const msg = history[i];
    const msgTokens = estimateTokens(msg.content as string);
    
    if (tokenCount + msgTokens <= maxInput) {
      historyToInclude.unshift(msg);
      tokenCount += msgTokens;
    } else {
      break;
    }
  }
  
  messages.push(...historyToInclude);
  
  return messages;
}

function formatFileContext(file: FileContext): string {
  return `File: ${file.path}\n\`\`\`${file.language}\n${file.content}\n\`\`\``;
}
```

---

## Token Estimation

```typescript
// Rough token estimation (4 chars ≈ 1 token for English)
function estimateTokens(text: string): number {
  // More accurate estimation
  const words = text.split(/\s+/).length;
  const chars = text.length;
  
  // Average of word-based and char-based estimates
  const wordEstimate = words * 1.3;
  const charEstimate = chars / 4;
  
  return Math.ceil((wordEstimate + charEstimate) / 2);
}

// Estimate for message array
function estimateMessagesTokens(messages: Message[]): number {
  let total = 0;
  
  for (const msg of messages) {
    // Role token overhead
    total += 4;
    
    // Content
    if (typeof msg.content === 'string') {
      total += estimateTokens(msg.content);
    } else if (Array.isArray(msg.content)) {
      for (const part of msg.content) {
        if (part.type === 'text' && part.text) {
          total += estimateTokens(part.text);
        } else if (part.type === 'image_url') {
          // Images use fixed token counts
          total += part.image_url?.detail === 'high' ? 765 : 85;
        }
      }
    }
    
    // Tool calls
    if (msg.tool_calls) {
      for (const tc of msg.tool_calls) {
        total += estimateTokens(tc.function.name);
        total += estimateTokens(tc.function.arguments);
      }
    }
  }
  
  return total;
}
```

---

## Request Validation

```typescript
interface ValidationResult {
  valid: boolean;
  errors: string[];
  warnings: string[];
}

function validateRequest(request: ChatRequest): ValidationResult {
  const errors: string[] = [];
  const warnings: string[] = [];
  
  // Required fields
  if (!request.model) {
    errors.push('Model is required');
  }
  
  if (!request.messages?.length) {
    errors.push('At least one message is required');
  }
  
  // Message validation
  for (let i = 0; i < (request.messages?.length ?? 0); i++) {
    const msg = request.messages![i];
    
    if (!['system', 'user', 'assistant', 'tool'].includes(msg.role)) {
      errors.push(`Invalid role "${msg.role}" at message ${i}`);
    }
    
    if (msg.role === 'tool' && !msg.tool_call_id) {
      errors.push(`Tool message at ${i} missing tool_call_id`);
    }
  }
  
  // Parameter ranges
  if (request.temperature !== undefined) {
    if (request.temperature < 0 || request.temperature > 2) {
      errors.push('Temperature must be between 0 and 2');
    }
  }
  
  if (request.top_p !== undefined) {
    if (request.top_p < 0 || request.top_p > 1) {
      errors.push('top_p must be between 0 and 1');
    }
  }
  
  // Warnings
  const tokenEstimate = estimateMessagesTokens(request.messages ?? []);
  if (tokenEstimate > 100000) {
    warnings.push(`Large context (~${tokenEstimate} tokens). May hit limits.`);
  }
  
  if (request.temperature === 0 && request.top_p === 0) {
    warnings.push('Both temperature and top_p are 0. Output will be deterministic.');
  }
  
  return {
    valid: errors.length === 0,
    errors,
    warnings
  };
}
```

---

## HTTP Request

```typescript
async function sendRequest(
  request: ChatRequest,
  apiKey: string
): Promise<Response> {
  const validation = validateRequest(request);
  if (!validation.valid) {
    throw new Error(`Invalid request: ${validation.errors.join(', ')}`);
  }
  
  return fetch('https://api.venice.ai/api/v1/chat/completions', {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
      'Authorization': `Bearer ${apiKey}`,
      'Accept': request.stream 
        ? 'text/event-stream' 
        : 'application/json'
    },
    body: JSON.stringify(request)
  });
}
```

---

## PureScript Types

```purescript
module Sidepanel.Venice.Request where

type ChatRequest =
  { model :: String
  , messages :: Array Message
  , temperature :: Maybe Number
  , maxTokens :: Maybe Int
  , stream :: Boolean
  , tools :: Maybe (Array Tool)
  }

type Message =
  { role :: Role
  , content :: String
  , toolCalls :: Maybe (Array ToolCall)
  , toolCallId :: Maybe String
  }

data Role = System | User | Assistant | Tool

buildRequest :: String -> Array Message -> ChatRequest
buildRequest model messages =
  { model
  , messages
  , temperature: Nothing
  , maxTokens: Nothing
  , stream: true
  , tools: Nothing
  }
```

---

## Related Specifications

- `17-VENICE-RESPONSE-PARSING.md` - Response handling
- `18-VENICE-ERROR-HANDLING.md` - Error handling
- `10-VENICE-API-OVERVIEW.md` - API overview

---

*"Well-built requests get well-formed responses."*
