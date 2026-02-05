# 38-LOGGING-MONITORING: Application Logging System

## Overview

Comprehensive logging for debugging, monitoring, and auditing. Structured logs with levels, categories, and contextual data.

---

## Log Levels

| Level | Value | Use Case |
|-------|-------|----------|
| `DEBUG` | 0 | Detailed debugging info |
| `INFO` | 1 | Normal operations |
| `WARN` | 2 | Potential issues |
| `ERROR` | 3 | Errors that need attention |
| `FATAL` | 4 | Critical failures |

---

## Log Structure

```typescript
interface LogEntry {
  // Identification
  id: string;
  timestamp: Date;
  
  // Classification
  level: LogLevel;
  category: LogCategory;
  
  // Content
  message: string;
  data?: Record<string, unknown>;
  
  // Context
  sessionId?: string;
  requestId?: string;
  userId?: string;
  
  // Error details
  error?: {
    name: string;
    message: string;
    stack?: string;
  };
  
  // Performance
  duration?: number;
}

type LogLevel = 'DEBUG' | 'INFO' | 'WARN' | 'ERROR' | 'FATAL';

type LogCategory =
  | 'websocket'
  | 'api'
  | 'database'
  | 'state'
  | 'ui'
  | 'plugin'
  | 'performance'
  | 'security';
```

---

## Logger Implementation

```typescript
// bridge/src/logging/logger.ts

class Logger {
  private minLevel: LogLevel = 'INFO';
  private outputs: LogOutput[] = [];
  private context: Record<string, unknown> = {};
  
  constructor(config: LogConfig) {
    this.minLevel = config.minLevel;
    this.setupOutputs(config);
  }
  
  private setupOutputs(config: LogConfig): void {
    // Console output (always)
    this.outputs.push(new ConsoleOutput());
    
    // File output (if configured)
    if (config.file) {
      this.outputs.push(new FileOutput(config.file.path, config.file.maxSize));
    }
    
    // Remote output (if configured)
    if (config.remote) {
      this.outputs.push(new RemoteOutput(config.remote.endpoint));
    }
  }
  
  setContext(context: Record<string, unknown>): void {
    this.context = { ...this.context, ...context };
  }
  
  clearContext(): void {
    this.context = {};
  }
  
  private log(level: LogLevel, category: LogCategory, message: string, data?: Record<string, unknown>): void {
    if (LOG_LEVELS[level] < LOG_LEVELS[this.minLevel]) {
      return;
    }
    
    const entry: LogEntry = {
      id: generateId(),
      timestamp: new Date(),
      level,
      category,
      message,
      data,
      ...this.context
    };
    
    for (const output of this.outputs) {
      output.write(entry);
    }
  }
  
  debug(category: LogCategory, message: string, data?: Record<string, unknown>): void {
    this.log('DEBUG', category, message, data);
  }
  
  info(category: LogCategory, message: string, data?: Record<string, unknown>): void {
    this.log('INFO', category, message, data);
  }
  
  warn(category: LogCategory, message: string, data?: Record<string, unknown>): void {
    this.log('WARN', category, message, data);
  }
  
  error(category: LogCategory, message: string, error?: Error, data?: Record<string, unknown>): void {
    this.log('ERROR', category, message, {
      ...data,
      error: error ? {
        name: error.name,
        message: error.message,
        stack: error.stack
      } : undefined
    });
  }
  
  fatal(category: LogCategory, message: string, error?: Error): void {
    this.log('FATAL', category, message, {
      error: error ? {
        name: error.name,
        message: error.message,
        stack: error.stack
      } : undefined
    });
  }
  
  // Performance logging
  time(category: LogCategory, label: string): () => void {
    const start = performance.now();
    return () => {
      const duration = performance.now() - start;
      this.debug(category, `${label} completed`, { duration, label });
    };
  }
  
  // Child logger with preset context
  child(context: Record<string, unknown>): Logger {
    const child = new Logger({ minLevel: this.minLevel });
    child.outputs = this.outputs;
    child.context = { ...this.context, ...context };
    return child;
  }
}

const LOG_LEVELS: Record<LogLevel, number> = {
  DEBUG: 0,
  INFO: 1,
  WARN: 2,
  ERROR: 3,
  FATAL: 4
};

export const logger = new Logger({
  minLevel: process.env.LOG_LEVEL as LogLevel ?? 'INFO',
  file: {
    path: './logs/sidepanel.log',
    maxSize: 10 * 1024 * 1024  // 10MB
  }
});
```

---

## Log Outputs

### Console Output

```typescript
class ConsoleOutput implements LogOutput {
  write(entry: LogEntry): void {
    const color = this.getColor(entry.level);
    const prefix = `[${entry.timestamp.toISOString()}] [${entry.level}] [${entry.category}]`;
    
    const args = [
      `${color}${prefix}\x1b[0m`,
      entry.message
    ];
    
    if (entry.data) {
      args.push(JSON.stringify(entry.data, null, 2));
    }
    
    switch (entry.level) {
      case 'ERROR':
      case 'FATAL':
        console.error(...args);
        break;
      case 'WARN':
        console.warn(...args);
        break;
      default:
        console.log(...args);
    }
  }
  
  private getColor(level: LogLevel): string {
    switch (level) {
      case 'DEBUG': return '\x1b[36m';  // Cyan
      case 'INFO': return '\x1b[32m';   // Green
      case 'WARN': return '\x1b[33m';   // Yellow
      case 'ERROR': return '\x1b[31m';  // Red
      case 'FATAL': return '\x1b[35m';  // Magenta
    }
  }
}
```

### File Output

```typescript
class FileOutput implements LogOutput {
  private stream: fs.WriteStream;
  private currentSize: number = 0;
  
  constructor(
    private path: string,
    private maxSize: number
  ) {
    this.stream = fs.createWriteStream(path, { flags: 'a' });
    this.currentSize = fs.existsSync(path) ? fs.statSync(path).size : 0;
  }
  
  write(entry: LogEntry): void {
    const line = JSON.stringify(entry) + '\n';
    
    // Rotate if needed
    if (this.currentSize + line.length > this.maxSize) {
      this.rotate();
    }
    
    this.stream.write(line);
    this.currentSize += line.length;
  }
  
  private rotate(): void {
    this.stream.end();
    
    const timestamp = new Date().toISOString().replace(/[:.]/g, '-');
    const rotatedPath = this.path.replace('.log', `-${timestamp}.log`);
    
    fs.renameSync(this.path, rotatedPath);
    
    this.stream = fs.createWriteStream(this.path, { flags: 'a' });
    this.currentSize = 0;
    
    // Clean old logs (keep last 5)
    this.cleanOldLogs();
  }
}
```

---

## Usage Examples

```typescript
// Basic logging
logger.info('websocket', 'Client connected', { clientId: 'abc123' });
logger.warn('api', 'Rate limit approaching', { remaining: 5 });
logger.error('database', 'Query failed', new Error('Connection timeout'));

// With context
logger.setContext({ sessionId: 'sess_123', userId: 'user_456' });
logger.info('state', 'Session updated');

// Performance timing
const done = logger.time('api', 'Venice API call');
await makeApiCall();
done();  // Logs: "Venice API call completed" with duration

// Child logger
const wsLogger = logger.child({ component: 'websocket' });
wsLogger.info('websocket', 'Message received');
```

---

## Log Categories by Component

### Bridge Server

```typescript
// WebSocket events
logger.info('websocket', 'Connection opened', { clientId });
logger.debug('websocket', 'Message received', { method, params });
logger.warn('websocket', 'Connection dropped', { reason });

// API calls
logger.info('api', 'Venice request', { model, tokens: estimatedTokens });
logger.debug('api', 'Response received', { status, balanceDiem });
logger.error('api', 'Request failed', error, { status: error.status });

// Database
logger.debug('database', 'Query executed', { query, duration });
logger.error('database', 'Query failed', error);
```

### Frontend (via FFI)

```typescript
// State changes
logger.debug('state', 'Action dispatched', { action: action.type });
logger.info('state', 'State updated', { changed: Object.keys(diff) });

// UI events
logger.debug('ui', 'Component mounted', { component: 'Dashboard' });
logger.info('ui', 'User action', { action: 'createSession' });
```

---

## Monitoring Dashboard

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  LOGS                                                    [Filter ▼] [⟳]   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Level: [All ▼]  Category: [All ▼]  Search: [________________]            │
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │ 14:32:05.123  INFO   websocket  Client connected                    │   │
│  │ 14:32:04.891  DEBUG  state      Action dispatched: Navigate         │   │
│  │ 14:32:04.567  INFO   api        Venice request                      │   │
│  │ 14:32:03.234  WARN   api        Rate limit: 5 remaining             │   │
│  │ 14:32:02.112  ERROR  database   Query timeout                       │   │
│  │                                                                      │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  Showing 50 of 1,234 entries                         [Load More]           │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Related Specifications

- `82-DEBUG-MODE.md` - Debug tools
- `80-ERROR-TAXONOMY.md` - Error handling
- `67-PERFORMANCE-PROFILER.md` - Performance monitoring

---

*"Good logs tell the story of what happened."*
