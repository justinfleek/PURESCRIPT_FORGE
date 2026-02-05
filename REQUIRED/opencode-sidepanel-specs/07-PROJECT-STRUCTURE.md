# 07-PROJECT-STRUCTURE: Directory Layout and Module Organization

## Overview

This document defines the complete project structure, explaining the purpose of every directory and key file. Understanding this layout is essential for navigating and contributing to the codebase.

---

## Top-Level Structure

```
opencode-sidepanel/
├── .github/                    # GitHub configuration
│   ├── workflows/              # CI/CD pipelines
│   └── ISSUE_TEMPLATE/         # Issue templates
│
├── bridge/                     # Node.js bridge server
├── frontend/                   # PureScript/Halogen UI
├── plugin/                     # OpenCode plugin
├── proofs/                     # Lean4 theorems (Phase 3)
├── specs/                      # This documentation
│
├── flake.nix                   # Nix flake definition
├── flake.lock                  # Locked dependencies
├── justfile                    # Task runner commands
├── README.md                   # Project overview
├── LICENSE                     # MIT License
└── .gitignore                  # Git ignore patterns
```

---

## Bridge Server (`bridge/`)

The Node.js server that coordinates between OpenCode, Venice API, and browser.

```
bridge/
├── src/
│   ├── index.ts                # Entry point
│   ├── server.ts               # HTTP/WebSocket server
│   ├── config.ts               # Configuration loading
│   │
│   ├── opencode/
│   │   ├── client.ts           # OpenCode SDK client
│   │   ├── events.ts           # Event handlers
│   │   └── types.ts            # OpenCode types
│   │
│   ├── venice/
│   │   ├── client.ts           # Venice API client
│   │   ├── balance.ts          # Balance extraction
│   │   ├── rate-limiter.ts     # Rate limit handling
│   │   └── types.ts            # Venice types
│   │
│   ├── websocket/
│   │   ├── manager.ts          # Connection management
│   │   ├── handlers.ts         # Message handlers
│   │   ├── protocol.ts         # JSON-RPC protocol
│   │   └── auth.ts             # Token authentication
│   │
│   ├── lean/
│   │   ├── proxy.ts            # LSP proxy
│   │   ├── goals.ts            # Goal state management
│   │   └── types.ts            # Lean types
│   │
│   ├── storage/
│   │   ├── database.ts         # SQLite wrapper
│   │   ├── sessions.ts         # Session persistence
│   │   ├── snapshots.ts        # State snapshots
│   │   └── migrations/         # Schema migrations
│   │       ├── 001_initial.sql
│   │       └── 002_snapshots.sql
│   │
│   ├── state/
│   │   ├── store.ts            # Central state store
│   │   ├── balance.ts          # Balance state
│   │   ├── session.ts          # Session state
│   │   └── metrics.ts          # Usage metrics
│   │
│   └── utils/
│       ├── logger.ts           # Structured logging
│       ├── crypto.ts           # Encryption utilities
│       ├── time.ts             # Time utilities
│       └── errors.ts           # Error definitions
│
├── test/
│   ├── unit/
│   │   ├── venice/
│   │   │   ├── balance.test.ts
│   │   │   └── rate-limiter.test.ts
│   │   └── state/
│   │       └── store.test.ts
│   │
│   ├── integration/
│   │   ├── websocket.test.ts
│   │   └── api-proxy.test.ts
│   │
│   └── fixtures/
│       ├── mock-responses.ts
│       └── test-data.ts
│
├── package.json                # Dependencies
├── tsconfig.json               # TypeScript config
├── vitest.config.ts            # Test configuration
└── README.md                   # Bridge-specific docs
```

### Key Bridge Files

| File | Purpose |
|------|---------|
| `src/index.ts` | Application entry point, initialization |
| `src/server.ts` | Express + WebSocket server setup |
| `src/venice/client.ts` | Venice API wrapper with balance extraction |
| `src/websocket/manager.ts` | WebSocket connection pool management |
| `src/storage/database.ts` | SQLite database interface |

---

## Frontend (`frontend/`)

PureScript/Halogen single-page application.

```
frontend/
├── src/
│   ├── Main.purs               # Entry point
│   ├── AppM.purs               # Application monad
│   ├── Router.purs             # SPA routing
│   ├── Config.purs             # Runtime config
│   │
│   ├── Api/
│   │   ├── Types.purs          # Shared API types
│   │   ├── WebSocket.purs      # WebSocket client
│   │   ├── Codec.purs          # JSON encoding/decoding
│   │   └── Errors.purs         # API error types
│   │
│   ├── State/
│   │   ├── AppState.purs       # Global state type
│   │   ├── Balance.purs        # Balance state
│   │   ├── Session.purs        # Session state
│   │   ├── Proof.purs          # Lean4 proof state
│   │   ├── Timeline.purs       # Timeline state
│   │   ├── Store.purs          # State store impl
│   │   └── Reducer.purs        # State transitions
│   │
│   ├── Components/
│   │   ├── App.purs            # Root component
│   │   ├── Dashboard.purs      # Main dashboard
│   │   ├── Sidebar.purs        # Navigation sidebar
│   │   │
│   │   ├── Balance/
│   │   │   ├── DiemTracker.purs
│   │   │   ├── Countdown.purs
│   │   │   ├── AlertBadge.purs
│   │   │   └── BalanceHistory.purs
│   │   │
│   │   ├── Usage/
│   │   │   ├── TokenChart.purs
│   │   │   ├── CostBreakdown.purs
│   │   │   ├── ModelUsage.purs
│   │   │   └── TimeRangeSelector.purs
│   │   │
│   │   ├── Session/
│   │   │   ├── SessionPanel.purs
│   │   │   ├── SessionList.purs
│   │   │   ├── MessageHistory.purs
│   │   │   └── SessionExport.purs
│   │   │
│   │   ├── Proof/
│   │   │   ├── ProofPanel.purs
│   │   │   ├── GoalDisplay.purs
│   │   │   ├── ContextView.purs
│   │   │   ├── TacticList.purs
│   │   │   └── TheoremLibrary.purs
│   │   │
│   │   ├── Timeline/
│   │   │   ├── TimelineView.purs
│   │   │   ├── Scrubber.purs
│   │   │   ├── SnapshotCard.purs
│   │   │   └── DiffView.purs
│   │   │
│   │   ├── Performance/
│   │   │   ├── FlameGraph.purs
│   │   │   ├── LatencyChart.purs
│   │   │   └── ToolTimings.purs
│   │   │
│   │   ├── Settings/
│   │   │   ├── SettingsPanel.purs
│   │   │   ├── AlertConfig.purs
│   │   │   ├── KeybindingConfig.purs
│   │   │   └── StorageConfig.purs
│   │   │
│   │   └── Common/
│   │       ├── Button.purs
│   │       ├── Card.purs
│   │       ├── Modal.purs
│   │       ├── Tooltip.purs
│   │       ├── Loading.purs
│   │       ├── ErrorDisplay.purs
│   │       └── Icon.purs
│   │
│   ├── Hooks/
│   │   ├── UseWebSocket.purs
│   │   ├── UseCountdown.purs
│   │   ├── UseKeyboard.purs
│   │   ├── UseLocalStorage.purs
│   │   └── UseTheme.purs
│   │
│   └── Utils/
│       ├── Time.purs           # Time formatting
│       ├── Format.purs         # Number/currency formatting
│       ├── Keyboard.purs       # Keyboard utilities
│       ├── Dom.purs            # DOM utilities
│       └── FFI/
│           ├── XTerm.purs      # xterm.js bindings
│           ├── Recharts.purs   # Recharts bindings
│           └── LocalStorage.purs
│
├── test/
│   ├── Main.purs               # Test entry
│   ├── State/
│   │   ├── ReducerSpec.purs
│   │   └── BalanceSpec.purs
│   ├── Components/
│   │   ├── CountdownSpec.purs
│   │   └── DiemTrackerSpec.purs
│   └── Property/
│       ├── BalanceProps.purs
│       └── TimeProps.purs
│
├── assets/
│   ├── index.html              # HTML shell
│   ├── styles/
│   │   ├── main.css            # Global styles
│   │   ├── variables.css       # CSS variables
│   │   ├── components/
│   │   │   ├── dashboard.css
│   │   │   ├── diem-tracker.css
│   │   │   ├── charts.css
│   │   │   └── ...
│   │   └── themes/
│   │       ├── dark.css
│   │       └── light.css
│   └── fonts/
│       └── JetBrainsMono/
│
├── spago.yaml                  # Package manager config
├── packages.dhall              # Package set (if needed)
└── README.md                   # Frontend-specific docs
```

### Key Frontend Files

| File | Purpose |
|------|---------|
| `src/Main.purs` | Application bootstrap |
| `src/AppM.purs` | Application monad with capabilities |
| `src/State/AppState.purs` | Global state type definition |
| `src/Components/Dashboard.purs` | Main dashboard composition |
| `src/Api/WebSocket.purs` | Bridge communication |

---

## Plugin (`plugin/`)

OpenCode plugin that bridges TUI and sidepanel.

```
plugin/
├── src/
│   ├── index.ts                # Plugin entry point
│   ├── handlers/
│   │   ├── session.ts          # Session event handlers
│   │   ├── message.ts          # Message event handlers
│   │   ├── tool.ts             # Tool event handlers
│   │   └── file.ts             # File event handlers
│   └── bridge/
│       ├── connection.ts       # Bridge connection
│       └── protocol.ts         # Communication protocol
│
├── package.json
├── tsconfig.json
└── README.md
```

---

## Lean4 Proofs (`proofs/`)

Formal verification theorems (Phase 3).

```
proofs/
├── Sidepanel/
│   ├── Types/
│   │   ├── Balance.lean        # Balance type definitions
│   │   ├── Session.lean        # Session types
│   │   └── Usage.lean          # Usage types
│   │
│   ├── Theorems/
│   │   ├── Balance.lean        # Balance invariants
│   │   ├── Monotonicity.lean   # Token monotonicity
│   │   ├── CostCalculation.lean# Cost correctness
│   │   └── Idempotence.lean    # Restore idempotence
│   │
│   └── Tactics/
│       └── Custom.lean         # Custom tactics
│
├── lakefile.lean               # Lake build config
├── lean-toolchain              # Lean version
└── README.md
```

---

## Specifications (`specs/`)

This documentation.

```
specs/
├── 00-SPEC-INDEX.md
├── 01-EXECUTIVE-SUMMARY.md
├── 02-SYSTEM-ARCHITECTURE.md
├── ... (80+ files)
└── README.md
```

---

## Configuration Files

### Root Level

| File | Purpose |
|------|---------|
| `flake.nix` | Nix flake definition |
| `flake.lock` | Pinned Nix dependencies |
| `justfile` | Task runner commands |
| `.gitignore` | Git ignore patterns |
| `.envrc` | Direnv configuration |

### justfile Commands

```just
# Development
dev:           # Start all services
build:         # Build all packages
test:          # Run all tests
fmt:           # Format all code

# Bridge
bridge-dev:    # Start bridge with watch
bridge-build:  # Build bridge
bridge-test:   # Test bridge

# Frontend
frontend-dev:  # Start frontend with watch
frontend-build:# Build frontend
frontend-test: # Test frontend

# Utilities
check-deps:    # Verify dependencies
store-api-key: # Store Venice API key
clean:         # Clean build artifacts
```

---

## Module Naming Conventions

### PureScript Modules

```
Sidepanel.                    # Root namespace
  Components.                 # UI components
    Balance.DiemTracker       # Specific component
  State.                      # State management
    Balance                   # State slice
  Api.                        # External communication
    WebSocket                 # WebSocket client
  Utils.                      # Utilities
    Time                      # Time helpers
  Hooks.                      # Custom hooks
    UseCountdown              # Specific hook
```

### TypeScript Modules

```
@sidepanel/bridge             # Package name
  /opencode/*                 # OpenCode integration
  /venice/*                   # Venice API
  /websocket/*                # WebSocket server
  /storage/*                  # Persistence
  /state/*                    # State management
```

---

## File Naming Conventions

| Type | Convention | Example |
|------|------------|---------|
| PureScript | PascalCase | `DiemTracker.purs` |
| TypeScript | kebab-case | `rate-limiter.ts` |
| CSS | kebab-case | `diem-tracker.css` |
| Test | suffix `.test.ts` or `Spec.purs` | `balance.test.ts` |
| Spec docs | numbered prefix | `12-DIEM-RESET.md` |

---

## Import Organization

### PureScript

```purescript
-- 1. Prelude
import Prelude

-- 2. Standard library
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)

-- 3. External packages
import Halogen as H

-- 4. Internal modules
import Sidepanel.State.Balance (BalanceState)
```

### TypeScript

```typescript
// 1. Node built-ins
import { EventEmitter } from 'events';

// 2. External packages
import { z } from 'zod';

// 3. Internal modules
import { extractBalance } from './venice/balance';
import type { Balance } from './types';
```

---

## Related Specifications

- `05-DEVELOPMENT-SETUP.md` - Environment setup
- `08-DEVELOPMENT-WORKFLOW.md` - Day-to-day workflow
- `40-PURESCRIPT-ARCHITECTURE.md` - Frontend patterns
- `30-BRIDGE-ARCHITECTURE.md` - Bridge patterns

---

*"A well-organized codebase is a readable codebase. Readability is maintainability."*
