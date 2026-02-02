# Bridge Server

Production-grade bridge server connecting OpenCode, Venice API, Lean LSP, and browser client.

## Architecture

- **HTTP Server**: Serves static files and health checks
- **WebSocket Server**: JSON-RPC 2.0 communication with browser
- **State Store**: Single source of truth for application state
- **Venice Proxy**: Proxies Venice API requests, extracts balance from headers
- **OpenCode Client**: Connects to OpenCode SDK, forwards events
- **Lean Proxy**: Forwards Lean4 LSP requests via MCP
- **Database**: SQLite persistence for snapshots and history

## Features

- ✅ WebSocket server with JSON-RPC 2.0
- ✅ State synchronization
- ✅ Venice API proxy with balance extraction
- ✅ Database schema for persistence
- ⏳ OpenCode client integration (pending SDK)
- ⏳ Lean LSP proxy (pending MCP setup)

## Development

```bash
# Install dependencies
npm install

# Development mode (watch)
npm run dev

# Build
npm run build

# Start production server
npm start
```

## Configuration

Environment variables:
- `SIDEPANEL_PORT` - Server port (default: 8765)
- `SIDEPANEL_HOST` - Server host (default: 127.0.0.1)
- `VENICE_API_KEY` - Venice API key
- `STORAGE_PATH` - Database path
- `LOG_LEVEL` - Log level (debug, info, warn, error)
- `LOG_FORMAT` - Log format (json, pretty)

## Production Standards

- ✅ TypeScript strict mode
- ✅ Error handling at all boundaries
- ✅ Graceful shutdown
- ✅ Health checks
- ✅ Structured logging
- ⏳ Comprehensive tests (pending)
- ⏳ E2E tests (pending)
