# 26-PLUGIN-DEVELOPMENT-GUIDE: Creating OpenCode Plugins

## Overview

This guide explains how to develop plugins for OpenCode that integrate with the sidepanel. Plugins can capture events, provide data, extend functionality, and create custom views.

---

## Plugin Architecture

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          OPENCODE PLUGIN SYSTEM                             │
│                                                                              │
│  ┌──────────────────┐     ┌──────────────────┐     ┌──────────────────┐   │
│  │   YOUR PLUGIN    │────►│   OPENCODE SDK   │────►│   SIDEPANEL      │   │
│  │                  │     │                  │     │   BRIDGE         │   │
│  │  - Event hooks   │     │  - Event bus     │     │                  │   │
│  │  - Data capture  │     │  - Plugin API    │     │  - WebSocket     │   │
│  │  - Custom logic  │     │  - Lifecycle     │     │  - State sync    │   │
│  │                  │     │                  │     │  - UI rendering  │   │
│  └──────────────────┘     └──────────────────┘     └──────────────────┘   │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Quick Start

### 1. Create Plugin Directory

```bash
mkdir -p ~/.config/opencode/plugins/my-sidepanel-plugin
cd ~/.config/opencode/plugins/my-sidepanel-plugin
```

### 2. Create manifest.json

```json
{
  "name": "my-sidepanel-plugin",
  "version": "1.0.0",
  "description": "My custom sidepanel integration",
  "main": "index.js",
  "opencode": {
    "minVersion": "0.5.0",
    "permissions": [
      "session.read",
      "session.write",
      "balance.read",
      "events.subscribe"
    ]
  },
  "sidepanel": {
    "bridge": true,
    "views": ["custom-view"]
  }
}
```

### 3. Create index.js

```javascript
// index.js
export default function plugin(opencode) {
  const { events, session, bridge } = opencode;
  
  // Subscribe to events
  events.on('message.created', (message) => {
    console.log('New message:', message.content);
    
    // Send to sidepanel bridge
    bridge.send('custom.message', {
      id: message.id,
      content: message.content,
      timestamp: Date.now()
    });
  });
  
  // Subscribe to balance updates
  events.on('balance.update', (balance) => {
    bridge.send('custom.balance', balance);
  });
  
  // Return cleanup function
  return () => {
    events.off('message.created');
    events.off('balance.update');
  };
}
```

### 4. Register in opencode.json

```json
{
  "plugins": [
    {
      "name": "sidepanel",
      "path": "~/.config/opencode/plugins/sidepanel-bridge"
    },
    {
      "name": "my-sidepanel-plugin",
      "path": "~/.config/opencode/plugins/my-sidepanel-plugin"
    }
  ]
}
```

---

## Available Events

### Session Events

| Event | Payload | Description |
|-------|---------|-------------|
| `session.created` | `Session` | New session started |
| `session.ended` | `{ id, reason }` | Session ended |
| `session.switched` | `{ from, to }` | Active session changed |

### Message Events

| Event | Payload | Description |
|-------|---------|-------------|
| `message.created` | `Message` | User/assistant message |
| `message.streaming` | `{ id, chunk }` | Streaming chunk |
| `message.completed` | `Message` | Message finished |
| `message.error` | `{ id, error }` | Message failed |

### Tool Events

| Event | Payload | Description |
|-------|---------|-------------|
| `tool.start` | `{ name, args }` | Tool execution started |
| `tool.progress` | `{ name, progress }` | Tool progress update |
| `tool.complete` | `{ name, result }` | Tool finished |
| `tool.error` | `{ name, error }` | Tool failed |

### Balance Events

| Event | Payload | Description |
|-------|---------|-------------|
| `balance.update` | `Balance` | Balance changed |
| `balance.warning` | `{ level, diem }` | Low balance warning |
| `balance.depleted` | `{}` | Balance exhausted |

### Provider Events

| Event | Payload | Description |
|-------|---------|-------------|
| `provider.request` | `{ model, tokens }` | API request starting |
| `provider.response` | `{ model, headers }` | API response received |
| `provider.error` | `{ error }` | API error |

---

## Plugin API

### OpenCode Object

```typescript
interface OpenCodePlugin {
  // Event system
  events: EventEmitter;
  
  // Session management
  session: {
    getCurrent(): Session | null;
    getAll(): Session[];
    create(title: string): Session;
    switch(id: string): void;
  };
  
  // Bridge communication
  bridge: {
    send(event: string, data: any): void;
    on(event: string, handler: (data: any) => void): void;
    request(method: string, params: any): Promise<any>;
  };
  
  // Storage
  storage: {
    get(key: string): any;
    set(key: string, value: any): void;
    delete(key: string): void;
  };
  
  // Configuration
  config: {
    get(key: string): any;
    set(key: string, value: any): void;
  };
  
  // Logging
  log: {
    debug(message: string, ...args: any[]): void;
    info(message: string, ...args: any[]): void;
    warn(message: string, ...args: any[]): void;
    error(message: string, ...args: any[]): void;
  };
}
```

---

## Bridge Communication

### Sending Data to Sidepanel

```javascript
// Send custom event
bridge.send('my-plugin.data', {
  type: 'custom',
  payload: { foo: 'bar' }
});

// Send with namespace
bridge.send('my-plugin.metric', {
  name: 'response_time',
  value: 123,
  unit: 'ms'
});
```

### Receiving from Sidepanel

```javascript
// Listen for sidepanel requests
bridge.on('my-plugin.request', async (data) => {
  const result = await processRequest(data);
  return result;  // Will be sent back as response
});
```

### Request/Response Pattern

```javascript
// Sidepanel can request data from plugin
bridge.on('my-plugin.get-stats', async () => {
  return {
    messagesProcessed: 100,
    tokensUsed: 50000,
    uptime: process.uptime()
  };
});
```

---

## Creating Custom Views

### Register View in Manifest

```json
{
  "sidepanel": {
    "views": [
      {
        "id": "my-custom-view",
        "title": "My View",
        "icon": "📊",
        "component": "views/MyView.jsx"
      }
    ]
  }
}
```

### View Component (React/Preact)

```jsx
// views/MyView.jsx
import { useState, useEffect } from 'preact/hooks';

export default function MyView({ bridge }) {
  const [data, setData] = useState(null);
  
  useEffect(() => {
    // Subscribe to plugin events
    const unsubscribe = bridge.on('my-plugin.data', (newData) => {
      setData(newData);
    });
    
    // Request initial data
    bridge.request('my-plugin.get-stats').then(setData);
    
    return unsubscribe;
  }, []);
  
  if (!data) return <div>Loading...</div>;
  
  return (
    <div className="my-view">
      <h2>My Custom View</h2>
      <div className="stats">
        <div>Messages: {data.messagesProcessed}</div>
        <div>Tokens: {data.tokensUsed}</div>
      </div>
    </div>
  );
}
```

---

## Complete Example: Token Tracker Plugin

```javascript
// index.js - Token tracking plugin with sidepanel integration

export default function tokenTrackerPlugin(opencode) {
  const { events, bridge, storage, log } = opencode;
  
  // Initialize state
  let sessionTokens = storage.get('sessionTokens') || {};
  let totalTokens = storage.get('totalTokens') || { prompt: 0, completion: 0 };
  
  // Track tokens per message
  events.on('message.completed', (message) => {
    if (message.role === 'assistant' && message.usage) {
      const { prompt_tokens, completion_tokens } = message.usage;
      
      // Update session totals
      const sessionId = opencode.session.getCurrent()?.id;
      if (sessionId) {
        sessionTokens[sessionId] = sessionTokens[sessionId] || { prompt: 0, completion: 0 };
        sessionTokens[sessionId].prompt += prompt_tokens;
        sessionTokens[sessionId].completion += completion_tokens;
      }
      
      // Update global totals
      totalTokens.prompt += prompt_tokens;
      totalTokens.completion += completion_tokens;
      
      // Persist
      storage.set('sessionTokens', sessionTokens);
      storage.set('totalTokens', totalTokens);
      
      // Send to sidepanel
      bridge.send('token-tracker.update', {
        session: sessionTokens[sessionId],
        total: totalTokens,
        lastMessage: { prompt_tokens, completion_tokens }
      });
      
      log.debug(`Tokens used: ${prompt_tokens} in, ${completion_tokens} out`);
    }
  });
  
  // Handle requests from sidepanel
  bridge.on('token-tracker.get-stats', () => {
    return {
      sessionTokens,
      totalTokens,
      sessionsTracked: Object.keys(sessionTokens).length
    };
  });
  
  bridge.on('token-tracker.reset', () => {
    sessionTokens = {};
    totalTokens = { prompt: 0, completion: 0 };
    storage.set('sessionTokens', sessionTokens);
    storage.set('totalTokens', totalTokens);
    
    bridge.send('token-tracker.update', {
      session: null,
      total: totalTokens
    });
    
    return { success: true };
  });
  
  // Cleanup
  return () => {
    events.off('message.completed');
    bridge.off('token-tracker.get-stats');
    bridge.off('token-tracker.reset');
  };
}
```

---

## Best Practices

### 1. Always Clean Up

```javascript
export default function plugin(opencode) {
  const handlers = [];
  
  handlers.push(
    opencode.events.on('event', handler)
  );
  
  // Return cleanup
  return () => {
    handlers.forEach(h => h.unsubscribe());
  };
}
```

### 2. Handle Errors Gracefully

```javascript
events.on('message.created', async (message) => {
  try {
    await processMessage(message);
  } catch (error) {
    log.error('Failed to process message:', error);
    // Don't throw - other plugins still need to run
  }
});
```

### 3. Namespace Your Events

```javascript
// Good
bridge.send('my-plugin.data', data);
bridge.send('my-plugin.error', error);

// Bad - could conflict with other plugins
bridge.send('data', data);
bridge.send('error', error);
```

### 4. Debounce Frequent Updates

```javascript
import { debounce } from 'lodash';

const sendUpdate = debounce((data) => {
  bridge.send('my-plugin.update', data);
}, 100);

events.on('message.streaming', (chunk) => {
  sendUpdate({ chunk });  // Won't spam the bridge
});
```

### 5. Validate Data

```javascript
bridge.on('my-plugin.action', (data) => {
  if (!data || typeof data.id !== 'string') {
    return { error: 'Invalid data' };
  }
  // Process valid data
});
```

---

## Testing Plugins

### Unit Testing

```javascript
import { createMockOpencode } from '@opencode/testing';
import myPlugin from './index.js';

describe('My Plugin', () => {
  let opencode;
  let cleanup;
  
  beforeEach(() => {
    opencode = createMockOpencode();
    cleanup = myPlugin(opencode);
  });
  
  afterEach(() => {
    cleanup();
  });
  
  it('sends data to bridge on message', () => {
    opencode.events.emit('message.created', { id: '1', content: 'test' });
    
    expect(opencode.bridge.send).toHaveBeenCalledWith(
      'my-plugin.message',
      expect.objectContaining({ id: '1' })
    );
  });
});
```

### Integration Testing

```javascript
// Use the real sidepanel bridge in test mode
import { startTestBridge } from '@sidepanel/testing';

describe('Plugin Integration', () => {
  let bridge;
  
  beforeAll(async () => {
    bridge = await startTestBridge();
  });
  
  it('receives data in sidepanel', async () => {
    // Emit event in plugin
    await bridge.emitPluginEvent('message.created', { id: '1' });
    
    // Check sidepanel received it
    const state = await bridge.getState();
    expect(state.messages).toContainEqual(
      expect.objectContaining({ id: '1' })
    );
  });
});
```

---

## Related Specifications

- `21-PLUGIN-SYSTEM.md` - Plugin system overview
- `22-SDK-INTEGRATION.md` - SDK details
- `31-WEBSOCKET-PROTOCOL.md` - Bridge protocol

---

*"Plugins extend the possible. Build what you need."*
