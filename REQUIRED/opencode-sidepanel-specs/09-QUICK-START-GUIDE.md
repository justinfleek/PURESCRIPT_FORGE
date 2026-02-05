# 09-QUICK-START-GUIDE: Up and Running in 5 Minutes

## Overview

This guide gets you from zero to a working sidepanel development environment in under 5 minutes.

---

## Prerequisites

- Node.js 20+
- Git
- Venice API key (get one at venice.ai)

---

## Quick Start

### 1. Clone and Install (1 minute)

```bash
# Clone the repository
git clone https://github.com/your-org/opencode-sidepanel.git
cd opencode-sidepanel

# Install dependencies
npm install
```

### 2. Configure Venice API (30 seconds)

```bash
# Copy environment template
cp .env.example .env

# Edit .env and add your Venice API key
echo "VENICE_API_KEY=your-key-here" >> .env
```

### 3. Start Development Server (30 seconds)

```bash
# Start the bridge server and frontend
npm run dev
```

This starts:
- Bridge server on `http://localhost:3000`
- Frontend dev server on `http://localhost:5173`
- WebSocket on `ws://localhost:3000/ws`

### 4. Open the Sidepanel (10 seconds)

Open your browser to `http://localhost:5173`

You should see:
- Dashboard with Diem balance (if Venice API is configured)
- Countdown to midnight UTC
- Empty session panel

### 5. Connect to OpenCode (Optional)

If you have OpenCode installed:

```bash
# In your project directory
opencode --config opencode.json
```

The sidepanel will automatically connect and start tracking sessions.

---

## Verify Installation

### Check Bridge Server

```bash
curl http://localhost:3000/health
# Should return: {"status":"ok","version":"0.1.0"}
```

### Check WebSocket

```bash
# Using websocat
websocat ws://localhost:3000/ws
# Type: {"jsonrpc":"2.0","method":"ping","id":1}
# Should receive: {"jsonrpc":"2.0","result":"pong","id":1}
```

### Check Venice Connection

Look at the dashboard - if your Diem balance shows a number (not "---"), Venice is connected.

---

## Common Issues

### "Cannot connect to bridge server"

```bash
# Check if port 3000 is in use
lsof -i :3000

# Kill existing process if needed
kill -9 <PID>

# Restart
npm run dev
```

### "Venice API error"

1. Verify your API key is correct in `.env`
2. Check Venice status at status.venice.ai
3. Ensure you have Diem balance remaining

### "WebSocket disconnecting"

This usually means the bridge server crashed. Check the terminal for errors.

```bash
# View logs
npm run dev 2>&1 | tee debug.log
```

---

## Next Steps

1. **Read the Architecture** - `02-SYSTEM-ARCHITECTURE.md`
2. **Understand Diem Tracking** - `11-DIEM-TRACKING.md`
3. **Explore the Dashboard** - `50-DASHBOARD-LAYOUT.md`
4. **Learn Keyboard Shortcuts** - Press `?` in the app

---

## Development Commands

```bash
# Start everything
npm run dev

# Run tests
npm test

# Build for production
npm run build

# Type check
npm run typecheck

# Lint
npm run lint

# Format
npm run format
```

---

## File Locations

| What | Where |
|------|-------|
| Bridge server | `bridge/src/` |
| Frontend | `frontend/src/` |
| Shared types | `shared/` |
| Tests | `**/test/` |
| Config | `*.config.*` |

---

*You're ready to start developing. Happy coding!*
