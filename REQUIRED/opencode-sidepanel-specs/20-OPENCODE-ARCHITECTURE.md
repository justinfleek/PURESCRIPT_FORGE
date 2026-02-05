# 20-OPENCODE-ARCHITECTURE: Understanding OpenCode

## Overview

OpenCode is a terminal-based AI coding assistant built in Go with Bubbletea. Understanding its architecture is essential for building a sidepanel that integrates seamlessly.

---

## OpenCode Structure

### High-Level Architecture

```
┌─────────────────────────────────────────────────────────────────────────┐
│                           OPENCODE TUI                                   │
│                                                                          │
│  ┌──────────────────────────────────────────────────────────────────┐   │
│  │                        BUBBLETEA MODEL                           │   │
│  │                                                                   │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────┐  │   │
│  │  │  Message    │  │   Chat      │  │    Tool Execution       │  │   │
│  │  │  Input      │  │   History   │  │    Panel                │  │   │
│  │  └─────────────┘  └─────────────┘  └─────────────────────────┘  │   │
│  │                                                                   │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────┐  │   │
│  │  │  Status     │  │   Model     │  │    File Tree            │  │   │
│  │  │  Bar        │  │   Selector  │  │    (optional)           │  │   │
│  │  └─────────────┘  └─────────────┘  └─────────────────────────┘  │   │
│  │                                                                   │   │
│  └──────────────────────────────────────────────────────────────────┘   │
│                              │                                           │
│                              ▼                                           │
│  ┌──────────────────────────────────────────────────────────────────┐   │
│  │                      CORE SERVICES                                │   │
│  │                                                                   │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────┐  │   │
│  │  │  Provider   │  │   Session   │  │    MCP Client           │  │   │
│  │  │  Manager    │  │   Manager   │  │                         │  │   │
│  │  └─────────────┘  └─────────────┘  └─────────────────────────┘  │   │
│  │                                                                   │   │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────┐  │   │
│  │  │  Tool       │  │   File      │  │    Plugin System        │  │   │
│  │  │  Executor   │  │   Watcher   │  │                         │  │   │
│  │  └─────────────┘  └─────────────┘  └─────────────────────────┘  │   │
│  │                                                                   │   │
│  └──────────────────────────────────────────────────────────────────┘   │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Core Concepts

### Sessions

A session represents a single conversation with the AI:

```go
type Session struct {
    ID          string
    Title       string
    Model       string
    Provider    string
    CreatedAt   time.Time
    UpdatedAt   time.Time
    Messages    []Message
    TokenUsage  TokenUsage
}

type TokenUsage struct {
    PromptTokens     int
    CompletionTokens int
    TotalTokens      int
    CachedTokens     int
}
```

Sessions are persisted to SQLite and can be resumed.

### Messages

Messages are the conversation turns:

```go
type Message struct {
    ID        string
    Role      string  // "user", "assistant", "system", "tool"
    Content   string
    ToolCalls []ToolCall
    ToolResults []ToolResult
    CreatedAt time.Time
    Usage     *MessageUsage
}

type MessageUsage struct {
    PromptTokens     int
    CompletionTokens int
    Model            string
    Cost             float64
}
```

### Tools

OpenCode has built-in tools for file operations, shell commands, etc.:

```go
type Tool struct {
    Name        string
    Description string
    Parameters  map[string]ToolParameter
}

// Built-in tools include:
// - read_file
// - write_file
// - list_directory
// - execute_command
// - search_files
// - web_search (if enabled)
```

### MCP Integration

OpenCode supports MCP servers for extended tool access:

```go
type MCPServer struct {
    Name      string
    Type      string  // "local" or "remote"
    Command   string
    Args      []string
    Env       map[string]string
}

// MCP tools appear alongside built-in tools
// Example: lean-lsp-mcp provides lean_goal, lean_completions, etc.
```

---

## Plugin System

### Plugin Interface

Plugins receive events and can interact with OpenCode:

```go
type Plugin interface {
    // Lifecycle
    Init(ctx context.Context, api PluginAPI) error
    Shutdown() error
    
    // Event handlers (all optional)
    OnSessionCreated(session *Session)
    OnSessionUpdated(session *Session)
    OnMessageCreated(message *Message)
    OnMessageCompleted(message *Message)
    OnToolExecuted(tool string, result *ToolResult, duration time.Duration)
    // ... more events
}

type PluginAPI interface {
    // Read access
    GetCurrentSession() *Session
    GetMessage(id string) *Message
    ListSessions() []*Session
    
    // Subscribe to events
    Subscribe(event string, handler EventHandler)
    
    // Limited write access
    SendNotification(title, body string)
}
```

### Plugin Loading

Plugins are loaded from configuration:

```json
{
  "plugin": ["opencode-sidepanel", "other-plugin"]
}
```

OpenCode looks for plugins in:
1. `~/.config/opencode/plugins/`
2. Global npm modules
3. Local `node_modules/`

---

## Provider System

### Provider Interface

Providers are AI model backends:

```go
type Provider interface {
    Name() string
    Models() []Model
    Chat(ctx context.Context, request ChatRequest) (ChatResponse, error)
    StreamChat(ctx context.Context, request ChatRequest) (<-chan StreamChunk, error)
}

type Model struct {
    ID          string
    Name        string
    ContextSize int
    InputCost   float64  // per 1K tokens
    OutputCost  float64  // per 1K tokens
}
```

### Built-in Providers

- **OpenAI** - GPT-4, GPT-3.5, etc.
- **Anthropic** - Claude 3, Claude 2
- **OpenRouter** - Multiple models via single API
- **Venice** - Venice.ai models
- **Local** - Ollama, LM Studio

### Venice Provider

Our target provider:

```go
type VeniceProvider struct {
    apiKey  string
    baseURL string
}

func (v *VeniceProvider) Chat(ctx context.Context, req ChatRequest) (ChatResponse, error) {
    // Make request to Venice API
    resp, err := v.client.Post(v.baseURL+"/chat/completions", req)
    
    // CRITICAL: Extract balance from headers
    // x-venice-balance-diem
    // x-venice-balance-usd
    
    return resp, err
}
```

---

## Serve Mode

When started with `--serve`, OpenCode exposes an HTTP server:

```go
func (app *App) StartServe(port int) error {
    // HTTP server for:
    // - Plugin communication
    // - SDK access
    // - Future: browser sidepanel
    
    mux := http.NewServeMux()
    mux.HandleFunc("/api/session", app.handleSession)
    mux.HandleFunc("/api/messages", app.handleMessages)
    mux.HandleFunc("/ws", app.handleWebSocket)
    
    return http.ListenAndServe(fmt.Sprintf(":%d", port), mux)
}
```

---

## Data Flow

### Message Lifecycle

```
User Input → Message Created → Provider Request → 
  Stream Chunks → Tool Calls (if any) → 
  Tool Execution → Tool Results → 
  Continue Response → Message Completed
```

### Event Emission

```go
func (app *App) sendMessage(content string) error {
    msg := &Message{
        ID:      uuid.New().String(),
        Role:    "user",
        Content: content,
    }
    
    // Emit event
    app.plugins.Emit("message.created", msg)
    
    // Send to provider
    response, err := app.provider.Chat(ctx, request)
    
    // Process tool calls
    for _, toolCall := range response.ToolCalls {
        result := app.executeTool(toolCall)
        app.plugins.Emit("tool.execute.after", toolCall.Name, result, duration)
    }
    
    // Emit completion
    app.plugins.Emit("message.completed", response.Message)
    
    return nil
}
```

---

## Configuration

### opencode.json

```json
{
  "$schema": "https://opencode.ai/config.json",
  
  "provider": "venice",
  "model": "llama-3.3-70b",
  
  "providers": {
    "venice": {
      "apiKeyEnv": "VENICE_API_KEY"
    }
  },
  
  "mcp": {
    "lean-lsp": {
      "type": "local",
      "command": "lean-lsp-mcp"
    }
  },
  
  "plugin": ["opencode-sidepanel"],
  
  "sidepanel": {
    "port": 8765
  }
}
```

### Environment Variables

```bash
OPENCODE_PROVIDER=venice
OPENCODE_MODEL=llama-3.3-70b
VENICE_API_KEY=vk_...
```

---

## SDK Access

### JavaScript/TypeScript SDK

```typescript
import { OpenCodeClient } from '@opencode-ai/sdk';

const client = new OpenCodeClient({
  port: 8765  // Serve mode port
});

// Event subscription
client.on('session.updated', (session) => {
  console.log('Session updated:', session.id);
});

client.on('message.completed', (message) => {
  console.log('Message completed:', message.usage);
});

// API access
const session = await client.getCurrentSession();
const messages = await client.getMessages(session.id);
```

---

## Our Integration Points

### 1. Plugin Events

We receive events via the plugin system:
- Session lifecycle
- Message lifecycle  
- Tool execution
- File operations

### 2. Provider Headers

We intercept Venice API responses to extract:
- `x-venice-balance-diem`
- `x-venice-balance-usd`
- Rate limit headers

### 3. MCP Tools

We configure lean-lsp-mcp for proof checking.

### 4. Serve Mode

We use the HTTP/WebSocket server for:
- Initial state sync
- Real-time updates
- SDK queries

---

## Key Integration Code

### Plugin Registration

```typescript
// plugin/src/index.ts
import { Plugin, PluginAPI } from '@opencode-ai/sdk';

export class SidepanelPlugin implements Plugin {
  private api: PluginAPI;
  private bridge: BridgeConnection;
  
  async init(ctx: Context, api: PluginAPI): Promise<void> {
    this.api = api;
    this.bridge = new BridgeConnection();
    
    // Forward all events to bridge
    api.subscribe('session.created', (s) => this.bridge.send('session.created', s));
    api.subscribe('session.updated', (s) => this.bridge.send('session.updated', s));
    api.subscribe('message.created', (m) => this.bridge.send('message.created', m));
    api.subscribe('message.completed', (m) => this.bridge.send('message.completed', m));
    api.subscribe('tool.execute.after', (t, r, d) => 
      this.bridge.send('tool.execute.after', { tool: t, result: r, duration: d })
    );
  }
  
  async shutdown(): Promise<void> {
    await this.bridge.close();
  }
}
```

---

## Related Specifications

- `21-PLUGIN-SYSTEM.md` - Event hooks detail
- `22-SDK-INTEGRATION.md` - SDK usage
- `24-MESSAGE-FLOW.md` - Message lifecycle
- `06-OPENCODE-CONFIG.md` - Configuration

---

*"Understand the system you're extending before you extend it."*
