# 00-SPEC-INDEX: OpenCode Sidepanel Specification Suite

## Project Identity

**Name:** OpenCode Sidepanel  
**Brand:** Fleek (⚡ Lightning bolt, Rainbow gradient, Fraunces typeface)  
**Codename:** Terminal Apostasy  
**Mission:** Convert terminal purists to "vibe coding" through technical excellence  
**Total Specifications:** 99 files

---

## Critical Implementation Rules

> **AGENTS: Read these rules before ANY implementation work**

### 1. FULL FILE READS ONLY
```
NEVER use grep, search patterns, or partial file views.
ALWAYS read complete files to understand context.
If you can't see the whole file, you can't understand it.
```

### 2. CODE IS TRUTH, TYPES DESCRIBE
```
Working code is ALWAYS correct.
NEVER delete code to satisfy TypeScript.
ALWAYS update type definitions to match working code.
```

### 3. READ BEFORE WRITE
```
Before implementing ANY feature:
1. Read ALL related spec files
2. Understand the full context
3. Then write code
```

---

## Complete Specification Map (99 Files)

### Core Foundation (00-09) — 10 files
| # | File | Description |
|---|------|-------------|
| 00 | SPEC-INDEX | This navigation index |
| 01 | EXECUTIVE-SUMMARY | Project overview, goals, success metrics |
| 02 | SYSTEM-ARCHITECTURE | 3-layer architecture, data flows |
| 03 | TECHNOLOGY-STACK | Tech choices with rationale |
| 04 | NIXOS-FLAKE | Complete flake.nix configuration |
| 05 | DEVELOPMENT-SETUP | Environment setup guide |
| 06 | OPENCODE-CONFIG | Plugin and MCP configuration |
| 07 | PROJECT-STRUCTURE | Directory layout |
| 08 | DEVELOPMENT-WORKFLOW | Git flow, PR process |
| 09 | CONTRIBUTING-GUIDELINES | How to contribute |

### Venice AI Integration (10-19) — 10 files
| # | File | Description |
|---|------|-------------|
| 10 | VENICE-API-OVERVIEW | API structure, auth, endpoints |
| 11 | DIEM-TRACKING | Balance extraction, consumption rate |
| 12 | DIEM-RESET-COUNTDOWN | UTC midnight calculation, display |
| 13 | TOKEN-USAGE-METRICS | Collection, aggregation, storage |
| 14 | RATE-LIMIT-HANDLING | Rate limits, backoff strategy |
| 15 | COST-PROJECTION | Forecasting, budget management |
| 16 | MODEL-SELECTION | Model picker, comparison |
| 17 | VENICE-RESPONSE-PARSING | Extracting data from responses |
| 18 | VENICE-ERROR-HANDLING | Error codes and recovery |
| 19 | VENICE-REQUEST-BUILDING | Constructing API requests |

### OpenCode Integration (20-29) — 10 files
| # | File | Description |
|---|------|-------------|
| 20 | OPENCODE-ARCHITECTURE | OpenCode internals overview |
| 21 | PLUGIN-SYSTEM | 32+ event hooks |
| 22 | SDK-INTEGRATION | JavaScript SDK usage |
| 23 | SESSION-MANAGEMENT | Session lifecycle |
| 24 | MULTI-SESSION + MESSAGE-FLOW | Multiple sessions, message handling |
| 25 | SESSION-BRANCHING + TOOL-EXECUTION | Fork conversations, tool timing |
| 26 | PLUGIN-DEVELOPMENT-GUIDE | How to create plugins |
| 27 | CONTEXT-WINDOW-MANAGEMENT | Managing AI context |
| 28 | CONVERSATION-HISTORY | Message history management |
| 29 | SYSTEM-PROMPTS | Managing AI system prompts |

### Bridge Server (30-39) — 10 files
| # | File | Description |
|---|------|-------------|
| 30 | BRIDGE-ARCHITECTURE | Node.js middleware design |
| 31 | WEBSOCKET-PROTOCOL | JSON-RPC 2.0 protocol |
| 32 | STATE-SYNCHRONIZATION | Bridge-browser state sync |
| 33 | API-PROXY | Venice API communication |
| 34 | DATABASE-SCHEMA | SQLite schema |
| 35 | CONNECTION-STATUS | WebSocket connection management |
| 36 | NOTIFICATION-SYSTEM | Toasts, alerts, messages |
| 37 | DATA-PERSISTENCE | Storage strategy, recovery |
| 38 | LOGGING-MONITORING | Application logging system |
| 39 | HEALTH-CHECKS | System health monitoring |

### PureScript Frontend (40-49) — 10 files
| # | File | Description |
|---|------|-------------|
| 40 | PURESCRIPT-ARCHITECTURE | AppM monad, routing, FFI |
| 41 | STATE-MANAGEMENT | State types, reducer |
| 42 | HALOGEN-COMPONENTS | Component patterns |
| 43 | ACCESSIBILITY | WCAG compliance, a11y |
| 44 | FFI-BINDINGS | JavaScript interop patterns |
| 45 | ROUTING | SPA navigation system |
| 46 | COMMAND-PALETTE | Universal command interface |
| 47 | THEMING | Dark mode, CSS variables |
| 48 | KEYBOARD-NAVIGATION | Vim bindings, command palette |
| 49 | SIDEBAR-NAVIGATION | Navigation component |

### UI Components (50-59) — 10 files
| # | File | Description |
|---|------|-------------|
| 50 | DASHBOARD-LAYOUT | Main dashboard composition |
| 51 | DIEM-TRACKER-WIDGET | Balance display component |
| 52 | COUNTDOWN-TIMER | Reset countdown component |
| 53 | TOKEN-USAGE-CHART | Recharts visualization |
| 54 | SESSION-PANEL | Session details view |
| 55 | SETTINGS-PANEL | Configuration UI |
| 56 | ALERT-SYSTEM | Notifications and warnings |
| 57 | TERMINAL-EMBED | xterm.js integration |
| 58 | FILE-CONTEXT-VIEW | Files in AI context |
| 59 | DIFF-VIEWER | AI change visualization |

### Lean4 & Advanced Features (60-69) — 10 files
| # | File | Description |
|---|------|-------------|
| 60 | LEAN4-INTEGRATION-OVERVIEW | MCP integration overview |
| 61 | PROOF-PANEL | Proof status display |
| 62 | TACTIC-SUGGESTIONS | AI-powered proof assistance |
| 63 | TIMELINE-VIEW | Time-travel debugging |
| 64 | SNAPSHOT-MANAGEMENT | State snapshots |
| 65 | SESSION-RECORDING | Record and playback |
| 66 | SEARCH-VIEW | Universal search |
| 67 | PERFORMANCE-PROFILER | Flame graphs, analytics |
| 68 | HELP-OVERLAY | Onboarding, shortcuts |
| 69 | QUICK-ACTIONS | Fast access to common tasks |

### Testing (70-79) — 10 files
| # | File | Description |
|---|------|-------------|
| 70 | TESTING-STRATEGY | Test pyramid, coverage targets |
| 71 | UNIT-TESTING | PureScript/TypeScript patterns |
| 72 | INTEGRATION-TESTING | API contract tests |
| 73 | E2E-TESTING | Playwright tests |
| 74 | TEST-FIXTURES | Reusable test data and mocks |
| 75 | TEST-COVERAGE | Coverage requirements |
| 76 | LOAD-TESTING | Performance and stress testing |
| 77 | MONITORING-DASHBOARD | Observability and metrics |
| 78 | BACKUP-RECOVERY | Data backup strategies |
| 79 | API-VERSIONING | Version management |

### Operations & Quality (80-89) — 10 files
| # | File | Description |
|---|------|-------------|
| 80 | ERROR-TAXONOMY | Error codes, recovery |
| 81 | CI-CD-CONFIGURATION | GitHub Actions pipelines |
| 82 | DEBUG-MODE | Developer tools, diagnostics |
| 83 | SECURITY-MODEL | Threat analysis, controls |
| 84 | RESPONSIVE-LAYOUT | Mobile, tablet adaptations |
| 85 | CODE-STYLE-GUIDE | Formatting conventions |
| 86 | EXPORT-FUNCTIONALITY | Data export, sharing |
| 87 | GLOSSARY | Term definitions |
| 88 | IMPORT-FUNCTIONALITY | Data import, restore |
| 89 | IMPLEMENTATION-ROADMAP | 20-week plan |

### Brand, Architecture & Proofs (90-99) — 9 files
| # | File | Description |
|---|------|-------------|
| 90 | FLEEK-BRAND-INTEGRATION | Design system, visual identity |
| 91 | DEPENDENCY-GRAPH | Spec & code dependencies |
| 92 | LEAN4-BACKEND-PROOFS | Formal verification (Lean4) |
| 93 | IMPORT-MAP | Complete module imports |
| 94 | FLEEK-CSS-TOKENS | Design token system |

---

## Fleek Brand Summary

```css
/* Primary Colors */
--fleek-blue: #0090ff;
--fleek-green: #32e48e;
--fleek-yellow: #ffe629;
--fleek-orange: #f76b15;

/* Typography */
--font-display: 'Fraunces', Georgia, serif;
--font-body: 'Inter', sans-serif;
--font-mono: 'JetBrains Mono', monospace;
```

### Brand Assets Included

```
/assets/brand/
├── fleek-logo.svg               # Full logo with wordmark
├── flk-logo-on-light.svg        # Light background variant
├── circuit-pattern-*.svg        # Background patterns
├── fleek-grain-*.svg            # Texture overlays
├── rainbow-*.svg                # Gradient elements
└── icon.svg                     # Lightning bolt favicon

/assets/fonts/
├── Fraunces-Medium.ttf
└── Fraunces-SemiBold.ttf
```

---

## Venice Diem Critical Facts

```
Reset Time:     Midnight UTC (00:00:00)
Balance Headers: x-venice-balance-diem, x-venice-balance-usd
Consumption:    Diem first, then USD
Daily Allocation: 1 Diem = $1 credit
Rollover:       NONE - unused Diem expires at reset
```

---

## Lean4 Proofs Summary

Formal verification provided for:
- **Balance invariants** - Non-negativity, consumption priority
- **Burn rate calculations** - Monotonicity, exhaustion timing
- **UTC reset logic** - Countdown correctness, boundary handling
- **Session state machine** - Valid transitions, terminal states
- **WebSocket states** - Connection lifecycle proofs
- **JSON-RPC compliance** - Request/response validity
- **Message ordering** - Sequence invariants
- **Database safety** - Optimistic locking, no duplicates

---

*Total specifications: 99 files*
*Last updated: January 2025*
