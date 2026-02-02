# 89-IMPLEMENTATION-ROADMAP: Detailed Phase Breakdown

## Overview

This document provides a week-by-week implementation plan for the OpenCode Sidepanel project. Total timeline: **20 weeks** to feature-complete.

**Start Date:** TBD  
**Target Completion:** TBD + 20 weeks  
**Team Size:** 1-2 senior engineers + 0.5 DevOps

---

## Phase 1: Foundation (Weeks 1-4)

**Goal:** Working sidepanel with Diem tracking and basic bridge

### Week 1: Project Setup

| Day | Task | Deliverable |
|-----|------|-------------|
| 1 | Initialize Nix flake | `flake.nix` with all dependencies |
| 1 | Setup PureScript project | `spago.yaml`, directory structure |
| 2 | Setup Node.js bridge project | `package.json`, TypeScript config |
| 2 | Configure build pipeline | `justfile` with dev/build/test commands |
| 3 | Create OpenCode plugin scaffold | Basic plugin that loads |
| 3 | Implement plugin → bridge HTTP | Events reach bridge server |
| 4 | Setup WebSocket server | Browser can connect |
| 5 | Create PureScript app shell | "Hello World" renders in browser |

**Acceptance Criteria:**
- [ ] `nix develop` enters working shell
- [ ] `just dev` starts all services
- [ ] Plugin loads in OpenCode without errors
- [ ] Browser connects to WebSocket
- [ ] Bidirectional ping/pong working

### Week 2: Venice API Integration

| Day | Task | Deliverable |
|-----|------|-------------|
| 1 | Implement Venice API client | TypeScript client with auth |
| 1 | Extract balance from headers | Balance parsing tested |
| 2 | Create balance state store | In-memory + SQLite persistence |
| 2 | Implement balance aggregation | Rate calculation working |
| 3 | WebSocket balance broadcasts | Browser receives updates |
| 4 | Basic PureScript balance display | Shows diem + usd |
| 5 | Integration test | Full flow: API → display |

**Acceptance Criteria:**
- [ ] Venice API calls succeed with auth
- [ ] Balance extracted from every response
- [ ] Rate calculation produces sensible numbers
- [ ] Browser shows current balance
- [ ] Balance persists across bridge restart

### Week 3: Countdown Timer

| Day | Task | Deliverable |
|-----|------|-------------|
| 1 | Implement UTC midnight calculation | Correct for all timezones |
| 2 | Create countdown logic | Hours, minutes, seconds |
| 2 | Handle reset detection | Balance jump triggers reset |
| 3 | PureScript countdown component | Ticks every second |
| 3 | Urgency level styling | Warning/critical states |
| 4 | Tooltip with local time | "Resets at 7:00 PM EST" |
| 5 | Edge case testing | Midnight crossing, sleep/wake |

**Acceptance Criteria:**
- [ ] Countdown accurate to UTC midnight
- [ ] Timer updates every second without drift
- [ ] Urgency colors at correct thresholds
- [ ] Reset detection works
- [ ] Local time tooltip shows correctly

### Week 4: Dashboard Layout

| Day | Task | Deliverable |
|-----|------|-------------|
| 1 | Design dashboard wireframe | Figma/sketch approved |
| 2 | Implement dashboard shell | Header, sidebar, main area |
| 2 | Create card components | Reusable card container |
| 3 | Integrate DiemTracker widget | Full widget in dashboard |
| 3 | Add connection status indicator | Shows connected/disconnected |
| 4 | Implement dark theme | CSS variables, consistent styling |
| 5 | End-to-end testing | Full Phase 1 flow |

**Acceptance Criteria:**
- [ ] Dashboard renders without errors
- [ ] DiemTracker shows real balance
- [ ] Countdown updates in real-time
- [ ] Reconnection works after disconnect
- [ ] Dark theme consistent throughout

### Phase 1 Deliverables Checklist

- [ ] Nix flake with reproducible build
- [ ] OpenCode plugin (loads and emits events)
- [ ] Bridge server (HTTP + WebSocket)
- [ ] Venice API client with balance extraction
- [ ] PureScript dashboard with DiemTracker
- [ ] Countdown timer to UTC midnight
- [ ] Dark theme styling
- [ ] Basic documentation

---

## Phase 2: Core Features (Weeks 5-10)

**Goal:** Full token tracking, session management, terminal embedding

### Week 5: Session State Sync

| Day | Task | Deliverable |
|-----|------|-------------|
| 1 | Define session state schema | TypeScript + PureScript types |
| 2 | Implement plugin session hooks | Capture all session events |
| 2 | Session state in bridge | Track active session |
| 3 | WebSocket session broadcasts | Browser receives updates |
| 4 | PureScript session component | Shows tokens, cost, model |
| 5 | Session persistence | Survives bridge restart |

**Acceptance Criteria:**
- [ ] All session events captured
- [ ] Token counts accurate
- [ ] Cost calculation correct
- [ ] Session displayed in UI
- [ ] State persists correctly

### Week 6: Token Usage Dashboard

| Day | Task | Deliverable |
|-----|------|-------------|
| 1 | Design usage charts | Wireframes approved |
| 2 | Implement Recharts wrapper | PureScript FFI |
| 2 | Create LineChart component | Basic chart renders |
| 3 | Token usage over time chart | Real data flowing |
| 4 | Cost breakdown by model | Pie/bar chart |
| 5 | Time range selector | Last hour/day/week |

**Acceptance Criteria:**
- [ ] Charts render with real data
- [ ] Time range filtering works
- [ ] Model breakdown accurate
- [ ] Responsive to window resize
- [ ] No performance issues

### Week 7: Message-Level Tracking

| Day | Task | Deliverable |
|-----|------|-------------|
| 1 | Implement message hooks | Capture message events |
| 2 | Per-message token tracking | Stored and displayed |
| 2 | Message cost calculation | Per-model pricing |
| 3 | Message list component | Shows recent messages |
| 4 | Message detail view | Expand to see tokens/cost |
| 5 | Export session data | JSON/markdown export |

**Acceptance Criteria:**
- [ ] Every message tracked
- [ ] Token counts match OpenCode
- [ ] Costs calculated correctly
- [ ] UI shows message history
- [ ] Export produces valid files

### Week 8: Keyboard Navigation

| Day | Task | Deliverable |
|-----|------|-------------|
| 1 | Design keybinding scheme | Document approved |
| 2 | Implement keyboard hook | Capture all keys |
| 2 | j/k navigation | List navigation |
| 3 | Command palette (Ctrl+Shift+P) | Shows all actions |
| 4 | Vim-style commands | :, /, gg, G |
| 5 | Focus management | Tab order, focus trap |

**Acceptance Criteria:**
- [ ] All navigation via keyboard
- [ ] Command palette functional
- [ ] Focus never lost
- [ ] No conflicts with browser
- [ ] Customizable (future)

### Week 9: Terminal Embedding

| Day | Task | Deliverable |
|-----|------|-------------|
| 1 | xterm.js FFI | PureScript bindings |
| 2 | Terminal component | Renders in browser |
| 2 | WebSocket → terminal data | PTY data flows |
| 3 | Terminal input handling | Send keystrokes back |
| 4 | Fit addon integration | Responsive sizing |
| 5 | Terminal ↔ native switching | Toggle works |

**Acceptance Criteria:**
- [ ] Terminal renders correctly
- [ ] Input/output works
- [ ] Resize handled
- [ ] Switching is seamless
- [ ] Performance acceptable

### Week 10: Settings & Configuration

| Day | Task | Deliverable |
|-----|------|-------------|
| 1 | Settings panel design | Wireframes approved |
| 2 | Settings component | Form rendering |
| 2 | Alert threshold config | User can change |
| 3 | Theme selection | (Only dark for now) |
| 4 | Keybinding display | Show current bindings |
| 5 | Settings persistence | LocalStorage + bridge |

**Acceptance Criteria:**
- [ ] Settings panel renders
- [ ] Changes persist
- [ ] Alerts respect new thresholds
- [ ] No settings cause crashes

### Phase 2 Deliverables Checklist

- [ ] Session state synchronization
- [ ] Token usage charts (line, pie, bar)
- [ ] Message-level tracking
- [ ] Session export (JSON/markdown)
- [ ] Full keyboard navigation
- [ ] Command palette
- [ ] Embedded terminal (xterm.js)
- [ ] Settings panel
- [ ] Alert configuration

---

## Phase 3: Lean4 Integration (Weeks 11-16)

**Goal:** Proof-aware development workflow

### Week 11: Lean LSP Setup

| Day | Task | Deliverable |
|-----|------|-------------|
| 1 | Install lean-lsp-mcp | Nix package |
| 2 | Configure MCP in OpenCode | Server starts |
| 2 | Bridge → LSP proxy | Forward messages |
| 3 | Test basic LSP communication | Goals returned |
| 4 | Error handling | Graceful failures |
| 5 | Connection status tracking | UI shows state |

**Acceptance Criteria:**
- [ ] lean-lsp-mcp starts via MCP
- [ ] Goals query returns results
- [ ] Errors don't crash system
- [ ] Status visible in UI

### Week 12: Proof Status Panel

| Day | Task | Deliverable |
|-----|------|-------------|
| 1 | Design proof panel | Wireframes approved |
| 2 | Goal display component | Shows current goals |
| 2 | Context display | Variables in scope |
| 3 | Diagnostic messages | Errors/warnings |
| 4 | Goal tree visualization | Nested goals |
| 5 | Integration testing | Real Lean files |

**Acceptance Criteria:**
- [ ] Goals display correctly
- [ ] Context shows all variables
- [ ] Diagnostics visible
- [ ] Updates on file change

### Week 13: Tactic Suggestions

| Day | Task | Deliverable |
|-----|------|-------------|
| 1 | Research LeanSearch API | Document integration |
| 2 | Implement completion request | Get suggestions |
| 3 | Suggestion list component | Shows tactics |
| 4 | Insert tactic action | Click to insert |
| 5 | Keyboard selection | j/k to navigate |

**Acceptance Criteria:**
- [ ] Suggestions appear
- [ ] Relevant to current goal
- [ ] Click/enter inserts
- [ ] Keyboard navigation works

### Week 14: Theorem Library

| Day | Task | Deliverable |
|-----|------|-------------|
| 1 | Design theorem storage | Schema |
| 2 | Extract verified theorems | From Lean files |
| 3 | Theorem list component | Browse library |
| 4 | Search theorems | By name, type |
| 5 | Use theorem in proof | Insert statement |

**Acceptance Criteria:**
- [ ] Theorems extracted
- [ ] Persisted to database
- [ ] Searchable
- [ ] Usable in proofs

### Week 15: Lean4 Error Handling

| Day | Task | Deliverable |
|-----|------|-------------|
| 1 | Catalog error types | Document all errors |
| 2 | Pretty error formatting | Human-readable |
| 3 | Error location linking | Click to jump |
| 4 | Suggested fixes | When available |
| 5 | Error history | Recent errors list |

**Acceptance Criteria:**
- [ ] All errors displayed nicely
- [ ] Location clicking works
- [ ] Fixes shown when available

### Week 16: Proof Integration Polish

| Day | Task | Deliverable |
|-----|------|-------------|
| 1-2 | Performance optimization | Debounce, cache |
| 3 | Edge case handling | Large files, slow LSP |
| 4 | Documentation | Proof workflow guide |
| 5 | End-to-end testing | Full proof session |

**Acceptance Criteria:**
- [ ] No lag on large files
- [ ] Handles LSP timeouts
- [ ] Documentation complete

### Phase 3 Deliverables Checklist

- [ ] lean-lsp-mcp integration
- [ ] Proof status panel
- [ ] Goal state display
- [ ] Context visualization
- [ ] Diagnostic messages
- [ ] Tactic suggestions
- [ ] Theorem library
- [ ] Error formatting
- [ ] Proof workflow documentation

---

## Phase 4: Polish (Weeks 17-20)

**Goal:** Time-travel debugging, flame graphs, production readiness

### Week 17: State Snapshots

| Day | Task | Deliverable |
|-----|------|-------------|
| 1 | Design snapshot schema | Document structure |
| 2 | Automatic snapshots | Before destructive ops |
| 3 | Manual snapshot creation | User-triggered |
| 4 | Snapshot storage | SQLite with cleanup |
| 5 | Snapshot list component | Browse snapshots |

**Acceptance Criteria:**
- [ ] Auto-snapshots work
- [ ] Manual snapshots work
- [ ] Storage bounded
- [ ] List renders correctly

### Week 18: Time-Travel UI

| Day | Task | Deliverable |
|-----|------|-------------|
| 1 | Timeline component design | Wireframes |
| 2 | Timeline scrubber | Drag to navigate |
| 3 | Snapshot preview | Hover to preview |
| 4 | Restore functionality | Click to restore |
| 5 | Diff visualization | What changed |

**Acceptance Criteria:**
- [ ] Timeline shows history
- [ ] Scrubbing works smoothly
- [ ] Restore works
- [ ] Changes visible

### Week 19: Flame Graphs

| Day | Task | Deliverable |
|-----|------|-------------|
| 1 | Tool timing collection | Track all durations |
| 2 | Flame graph component | Basic visualization |
| 3 | Interactive zoom | Click to drill down |
| 4 | Differential comparison | Before/after |
| 5 | Export flame graph | SVG/PNG |

**Acceptance Criteria:**
- [ ] Timings collected
- [ ] Flame graph renders
- [ ] Zoom works
- [ ] Comparison works

### Week 20: Production Readiness

| Day | Task | Deliverable |
|-----|------|-------------|
| 1 | Performance audit | Identify issues |
| 2 | Bundle optimization | Tree shaking, minify |
| 3 | Error boundary | Graceful failures |
| 4 | Documentation | User guide, API docs |
| 5 | Release preparation | Changelog, version |

**Acceptance Criteria:**
- [ ] Bundle < 200KB gzipped
- [ ] No memory leaks
- [ ] Errors handled gracefully
- [ ] Docs complete
- [ ] Ready for release

### Phase 4 Deliverables Checklist

- [ ] State snapshot system
- [ ] Time-travel UI
- [ ] Timeline scrubber
- [ ] Restore functionality
- [ ] Flame graph visualization
- [ ] Performance optimization
- [ ] Error boundaries
- [ ] User documentation
- [ ] Release v0.1.0

---

## Risk Mitigation Schedule

| Week | Risk Check | Mitigation Action |
|------|------------|-------------------|
| 2 | Venice API access | Fallback to mock data |
| 4 | Phase 1 scope | Cut features, ship MVP |
| 8 | Performance issues | Profile and optimize |
| 11 | Lean LSP availability | Mock LSP for testing |
| 15 | Lean4 complexity | Reduce scope if needed |
| 18 | Time-travel complexity | Ship without diff |
| 20 | Release readiness | Extend if critical issues |

---

## Success Metrics by Phase

### Phase 1 Success
- [ ] Plugin loads in < 1 second
- [ ] Balance updates in < 100ms
- [ ] Countdown accurate to ±1 second
- [ ] Zero crashes during demo

### Phase 2 Success
- [ ] All token counts accurate
- [ ] Charts render in < 500ms
- [ ] Keyboard navigation complete
- [ ] Terminal usable for coding

### Phase 3 Success
- [ ] Proof goals display correctly
- [ ] Tactic suggestions helpful
- [ ] Theorem library searchable
- [ ] Lean workflow documented

### Phase 4 Success
- [ ] Time-travel works reliably
- [ ] Flame graphs actionable
- [ ] Bundle size < 200KB
- [ ] Documentation complete

---

## Dependencies

### External Dependencies
- Venice API (stable, documented)
- OpenCode plugin system (pre-1.0, may change)
- lean-lsp-mcp (active development)
- PureScript ecosystem (stable)
- Nix (stable)

### Internal Dependencies
```
Phase 2 depends on Phase 1 completion
Phase 3 depends on Phase 2 (bridge, WebSocket)
Phase 4 depends on Phase 2 (state management)
Phase 3 and 4 can partially parallel
```

---

## Team Allocation

### Weeks 1-10 (Foundation + Core)
- **Engineer A:** Bridge server, Venice integration
- **Engineer B:** PureScript frontend, components

### Weeks 11-16 (Lean4)
- **Engineer A:** LSP proxy, MCP integration
- **Engineer B:** Proof panel, suggestions UI
- **Lean Specialist:** Theorem library, proof patterns

### Weeks 17-20 (Polish)
- **Engineer A:** Snapshots, time-travel
- **Engineer B:** Flame graphs, optimization
- **DevOps:** CI/CD, release pipeline

---

*"A plan is nothing, but planning is everything." — Eisenhower*
