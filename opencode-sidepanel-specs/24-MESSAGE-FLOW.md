# 24-MESSAGE-FLOW: Message Lifecycle Handling

## Overview

This document details how messages flow through the system, from user input through AI response to UI update, including streaming, tool calls, and error handling.

---

## Message Lifecycle

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           MESSAGE LIFECYCLE                                  │
│                                                                              │
│  ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐             │
│  │  USER    │───►│ OPENCODE │───►│  VENICE  │───►│  STREAM  │             │
│  │  INPUT   │    │  CLIENT  │    │   API    │    │ RESPONSE │             │
│  └──────────┘    └──────────┘    └──────────┘    └──────────┘             │
│       │               │               │               │                     │
│       │               ▼               │               ▼                     │
│       │         ┌──────────┐          │         ┌──────────┐               │
│       │         │  PLUGIN  │          │         │  PARSE   │               │
│       │         │  EVENT   │          │         │  CHUNKS  │               │
│       │         └──────────┘          │         └──────────┘               │
│       │               │               │               │                     │
│       │               ▼               │               ▼                     │
│       │         ┌──────────┐          │         ┌──────────┐               │
│       └────────►│  BRIDGE  │◄─────────┘         │  TOOL    │               │
│                 │  SERVER  │◄───────────────────│  CALLS?  │               │
│                 └──────────┘                    └──────────┘               │
│                      │                               │                      │
│                      ▼                               ▼                      │
│                 ┌──────────┐                   ┌──────────┐                │
│                 │BROADCAST │                   │ EXECUTE  │                │
│                 │TO BROWSER│                   │  TOOLS   │                │
│                 └──────────┘                   └──────────┘                │
│                      │                               │                      │
│                      ▼                               ▼                      │
│                 ┌──────────┐                   ┌──────────┐                │
│                 │  UPDATE  │◄──────────────────│ CONTINUE │                │
│                 │    UI    │                   │ RESPONSE │                │
│                 └──────────┘                   └──────────┘                │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Event Types

### Plugin Events (from OpenCode)

```typescript
// Message created (user or assistant)
interface MessageCreatedEvent {
  type: 'message.created';
  message: {
    id: string;
    role: 'user' | 'assistant' | 'system';
    content: string;
    timestamp: Date;
  };
  session: {
    id: string;
    model: string;
  };
}

// Stream chunk (during assistant response)
interface StreamChunkEvent {
  type: 'stream.chunk';
  messageId: string;
  chunk: string;
  tokenCount?: number;
}

// Message completed (with usage)
interface MessageCompletedEvent {
  type: 'message.completed';
  message: {
    id: string;
    role: 'assistant';
    content: string;
    usage: {
      promptTokens: number;
      completionTokens: number;
      totalTokens: number;
      model: string;
    };
    toolCalls?: ToolCall[];
  };
}

// Tool execution
interface ToolExecuteEvent {
  type: 'tool.execute.before' | 'tool.execute.after';
  tool: string;
  args: any;
  result?: any;
  duration?: number;
  error?: Error;
}
```

---

## Bridge Processing

### Event Handler

```typescript
// bridge/src/opencode/event-handler.ts

export class OpenCodeEventHandler {
  private store: StateStore;
  private wsManager: WebSocketManager;
  private contextTracker: ContextTracker;
  private performanceCollector: PerformanceCollector;
  
  constructor(deps: Dependencies) {
    this.store = deps.store;
    this.wsManager = deps.wsManager;
    this.contextTracker = deps.contextTracker;
    this.performanceCollector = deps.performanceCollector;
  }
  
  // User sends a message
  handleMessageCreated(event: MessageCreatedEvent): void {
    if (event.message.role === 'user') {
      // Update session state
      this.store.updateSession({
        lastActivity: new Date(),
        messageCount: (this.store.getState().session?.messageCount ?? 0) + 1
      });
      
      // Broadcast to browser
      this.wsManager.broadcast({
        jsonrpc: '2.0',
        method: 'message.user',
        params: {
          id: event.message.id,
          content: event.message.content,
          timestamp: event.message.timestamp
        }
      });
      
      // Start performance tracking
      this.performanceCollector.startEvent(
        'user_input',
        'User Message',
        { content: event.message.content.slice(0, 100) }
      );
    }
  }
  
  // AI starts responding (streaming)
  handleStreamStart(messageId: string): void {
    this.wsManager.broadcast({
      jsonrpc: '2.0',
      method: 'message.assistant.start',
      params: { id: messageId }
    });
    
    // Start tracking AI response time
    this.performanceCollector.startEvent(
      'ai_response',
      'AI Response',
      { messageId }
    );
  }
  
  // Stream chunk arrives
  handleStreamChunk(event: StreamChunkEvent): void {
    // Broadcast chunk for live typing effect
    this.wsManager.broadcast({
      jsonrpc: '2.0',
      method: 'message.assistant.chunk',
      params: {
        id: event.messageId,
        chunk: event.chunk
      }
    });
  }
  
  // Message completed
  handleMessageCompleted(event: MessageCompletedEvent): void {
    const { message } = event;
    
    // End performance tracking
    this.performanceCollector.endEvent(message.id);
    
    // Update session metrics
    this.store.updateSession({
      promptTokens: (this.store.getState().session?.promptTokens ?? 0) + message.usage.promptTokens,
      completionTokens: (this.store.getState().session?.completionTokens ?? 0) + message.usage.completionTokens,
      cost: (this.store.getState().session?.cost ?? 0) + this.calculateCost(message.usage)
    });
    
    // Broadcast completion
    this.wsManager.broadcast({
      jsonrpc: '2.0',
      method: 'message.assistant.complete',
      params: {
        id: message.id,
        content: message.content,
        usage: message.usage,
        toolCalls: message.toolCalls
      }
    });
    
    // Handle tool calls if present
    if (message.toolCalls?.length) {
      for (const toolCall of message.toolCalls) {
        this.handleToolCallStart(toolCall);
      }
    }
  }
  
  // Tool execution starts
  handleToolExecuteBefore(event: ToolExecuteEvent): void {
    // Track file reads for context
    if (event.tool === 'read_file') {
      this.contextTracker.onFileReadStart(event.args.path);
    }
    
    // Broadcast to browser
    this.wsManager.broadcast({
      jsonrpc: '2.0',
      method: 'tool.start',
      params: {
        tool: event.tool,
        args: event.args
      }
    });
    
    // Performance tracking
    this.performanceCollector.startEvent(
      'tool_execution',
      `${event.tool}`,
      { tool: event.tool, args: event.args }
    );
  }
  
  // Tool execution completes
  handleToolExecuteAfter(event: ToolExecuteEvent): void {
    // Track file operations
    if (event.tool === 'read_file' && !event.error) {
      this.contextTracker.onFileRead({
        path: event.args.path,
        content: event.result
      });
    } else if (event.tool === 'write_file' && !event.error) {
      this.contextTracker.onFileWritten({
        path: event.args.path,
        content: event.args.content
      });
    }
    
    // End performance tracking
    this.performanceCollector.endEvent(event.tool);
    
    // Broadcast result
    this.wsManager.broadcast({
      jsonrpc: '2.0',
      method: 'tool.complete',
      params: {
        tool: event.tool,
        result: event.result,
        duration: event.duration,
        error: event.error?.message
      }
    });
  }
}
```

---

## Browser-Side Handling

### Message Reducer

```purescript
module Sidepanel.State.MessageReducer where

-- Handle incoming message events
reduceMessageAction :: MessageAction -> State -> State
reduceMessageAction action state = case action of
  
  UserMessage msg ->
    let newMessage = 
          { id: msg.id
          , role: User
          , content: msg.content
          , timestamp: msg.timestamp
          , usage: Nothing
          , toolCalls: []
          , status: Complete
          }
    in state 
      { session = map (addMessage newMessage) state.session }
  
  AssistantStart msgId ->
    let newMessage =
          { id: msgId
          , role: Assistant
          , content: ""
          , timestamp: now
          , usage: Nothing
          , toolCalls: []
          , status: Streaming
          }
    in state
      { session = map (addMessage newMessage) state.session
      , streamingMessageId = Just msgId
      }
  
  AssistantChunk { id, chunk } ->
    state
      { session = map (appendToMessage id chunk) state.session }
  
  AssistantComplete { id, content, usage, toolCalls } ->
    state
      { session = map (completeMessage id content usage toolCalls) state.session
      , streamingMessageId = Nothing
      }
  
  ToolStart { tool, args } ->
    let toolCall = { name: tool, args, status: Running, result: Nothing, duration: Nothing }
    in state
      { session = map (addToolCall toolCall) state.session
      , activeTools = Set.insert tool state.activeTools
      }
  
  ToolComplete { tool, result, duration, error } ->
    state
      { session = map (completeToolCall tool result duration error) state.session
      , activeTools = Set.delete tool state.activeTools
      }

-- Helper functions
addMessage :: Message -> Session -> Session
addMessage msg session = session { messages = snoc session.messages msg }

appendToMessage :: String -> String -> Session -> Session
appendToMessage msgId chunk session =
  session { messages = map updateIfMatch session.messages }
  where
    updateIfMatch msg
      | msg.id == msgId = msg { content = msg.content <> chunk }
      | otherwise = msg

completeMessage :: String -> String -> Usage -> Array ToolCall -> Session -> Session
completeMessage msgId content usage toolCalls session =
  session 
    { messages = map updateIfMatch session.messages
    , promptTokens = session.promptTokens + usage.promptTokens
    , completionTokens = session.completionTokens + usage.completionTokens
    , cost = session.cost + calculateCost usage
    }
  where
    updateIfMatch msg
      | msg.id == msgId = msg 
          { content = content
          , usage = Just usage
          , toolCalls = toolCalls
          , status = Complete
          }
      | otherwise = msg
```

### Streaming Message Component

```purescript
module Sidepanel.Components.StreamingMessage where

-- Render message with live typing effect
renderMessage :: forall m. Message -> H.ComponentHTML Action () m
renderMessage msg = case msg.status of
  Streaming ->
    HH.div
      [ HP.class_ (H.ClassName "message message--streaming") ]
      [ renderAvatar msg.role
      , HH.div
          [ HP.class_ (H.ClassName "message__content") ]
          [ HH.text msg.content
          , HH.span [ HP.class_ (H.ClassName "typing-cursor") ] [ HH.text "▋" ]
          ]
      ]
  
  Complete ->
    HH.div
      [ HP.class_ (H.ClassName "message") ]
      [ renderAvatar msg.role
      , HH.div
          [ HP.class_ (H.ClassName "message__content") ]
          [ renderMarkdown msg.content
          , renderToolCalls msg.toolCalls
          , renderUsage msg.usage
          ]
      ]

renderToolCalls :: forall m. Array ToolCall -> H.ComponentHTML Action () m
renderToolCalls toolCalls =
  when (not $ null toolCalls) $
    HH.div
      [ HP.class_ (H.ClassName "message__tools") ]
      (map renderToolCall toolCalls)

renderToolCall :: forall m. ToolCall -> H.ComponentHTML Action () m
renderToolCall { name, status, duration } =
  HH.div
    [ HP.classes $ toolCallClasses status ]
    [ HH.span [ HP.class_ (H.ClassName "tool-icon") ] [ HH.text $ statusIcon status ]
    , HH.span [ HP.class_ (H.ClassName "tool-name") ] [ HH.text name ]
    , case duration of
        Just d -> HH.span [ HP.class_ (H.ClassName "tool-duration") ] [ HH.text $ show d <> "ms" ]
        Nothing -> HH.text ""
    ]

statusIcon :: ToolStatus -> String
statusIcon = case _ of
  Pending -> "⏳"
  Running -> "🔄"
  Complete -> "✓"
  Error -> "✗"
```

---

## Error Handling

```typescript
// Handle errors at each stage
handleError(error: Error, context: ErrorContext): void {
  // Log error
  logger.error('Message flow error', { error, context });
  
  // Update state
  this.store.updateSession({
    lastError: error.message
  });
  
  // Broadcast to browser
  this.wsManager.broadcast({
    jsonrpc: '2.0',
    method: 'error',
    params: {
      type: context.type,
      message: error.message,
      recoverable: this.isRecoverable(error),
      action: this.suggestAction(error)
    }
  });
  
  // End any open performance events
  this.performanceCollector.endEventWithError(context.eventId, error);
}
```

---

## WebSocket Messages

### Browser → Bridge

```typescript
// Request message history
{ method: 'messages.list', params: { sessionId: string, limit?: number } }

// Request specific message
{ method: 'messages.get', params: { messageId: string } }
```

### Bridge → Browser

```typescript
// User message received
{ method: 'message.user', params: { id, content, timestamp } }

// Assistant starts responding
{ method: 'message.assistant.start', params: { id } }

// Streaming chunk
{ method: 'message.assistant.chunk', params: { id, chunk } }

// Response complete
{ method: 'message.assistant.complete', params: { id, content, usage, toolCalls } }

// Tool events
{ method: 'tool.start', params: { tool, args } }
{ method: 'tool.complete', params: { tool, result, duration, error? } }
```

---

## Related Specifications

- `21-PLUGIN-SYSTEM.md` - Event hooks
- `31-WEBSOCKET-PROTOCOL.md` - Message protocol
- `25-TOOL-EXECUTION.md` - Tool handling

---

*"Every message tells a story. Capture every detail."*
