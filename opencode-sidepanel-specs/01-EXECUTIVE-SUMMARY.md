# 01-EXECUTIVE-SUMMARY: OpenCode Sidepanel Project Overview

## The Opportunity

Terminal-based development tools are experiencing a renaissance. OpenCode, Claude Code, and similar TUI-first AI coding assistants appeal to senior engineers who value keyboard efficiency and minimal resource usage. However, these tools lack the visual richness that makes complex information—token costs, proof states, performance metrics—immediately comprehensible.

**The gap:** Senior engineers want terminal efficiency AND visual intelligence. They shouldn't have to choose.

**Our solution:** A hybrid sidepanel that extends OpenCode with a browser-based GUI, providing real-time visualization while preserving full terminal control. One click pops out to browser; one click returns to terminal. Best of both worlds.

---

## Target Users

### Primary: The Terminal Purist
- **Profile:** 10+ years experience, ex-FAANG, possibly HFT background
- **Current tools:** neovim/emacs, tmux, CLI everything
- **Pain points:** Dismisses "vibe coding" as amateur, but secretly curious
- **What converts them:** Seeing technical excellence they can't replicate themselves

### Secondary: The Pragmatic Senior
- **Profile:** Uses Cursor/VSCode but misses terminal efficiency
- **Current tools:** Mixed IDE and terminal workflow
- **Pain points:** Context switching, IDE resource usage
- **What converts them:** Terminal speed with IDE visualization

### Tertiary: The Formal Methods Enthusiast
- **Profile:** Values correctness, uses types heavily, interested in proofs
- **Current tools:** Haskell/Rust/OCaml, maybe Lean4/Coq curious
- **Pain points:** No AI tools understand formal verification
- **What converts them:** Lean4 integration with proof-aware assistance

---

## Core Value Propositions

### 1. Venice Diem Visibility (Phase 1)
**Problem:** Token costs are invisible until the bill arrives.

**Solution:** Real-time Diem balance tracking with:
- Current balance display (Diem + USD equivalent)
- Countdown timer to midnight UTC reset
- Usage rate visualization (tokens/minute, cost/hour)
- Budget projection ("At current rate, depleted in 4h 23m")
- Alert thresholds (yellow at 20%, red at 5%)

**Why it matters:** HFT engineers think in budgets and burn rates. Showing them their AI spend in familiar terms builds trust.

### 2. Bidirectional Terminal↔Browser (Phase 1-2)
**Problem:** Terminal tools lack visualization; GUIs lack efficiency.

**Solution:** Seamless switching between interfaces:
- `opencode serve --sidepanel` starts HTTP server
- Browser opens automatically (or manual URL)
- One-click "Pop to Browser" from terminal
- One-click "Back to Terminal" from browser
- Shared state—both views always synchronized

**Why it matters:** No compromise. Full terminal power. Full visual richness. User chooses moment-to-moment.

### 3. Lean4 Proof Integration (Phase 3)
**Problem:** AI coding assistants can't verify correctness.

**Solution:** Integrated theorem proving:
- Proof status panel showing current goals
- Tactic suggestions from LeanSearch
- Theorem library with persistent verified invariants
- "Your code is mathematically correct" status indicator

**Why it matters:** This is the differentiator Cursor can't match. Formal verification integrated into the coding workflow.

### 4. Time-Travel Debugging (Phase 4)
**Problem:** "What did I just break?" is unanswerable.

**Solution:** Full session state history:
- Append-only event log of all state changes
- Snapshot points before destructive operations
- Visual timeline with scrubber
- One-click restore to any previous state
- Shareable session recordings for review

**Why it matters:** Senior engineers debug by understanding state evolution. Give them a time machine.

### 5. Performance Flame Graphs (Phase 4)
**Problem:** "Why is this slow?" requires external tooling.

**Solution:** Built-in performance visualization:
- Plugin hook execution times
- API call latency breakdown
- Token processing rates
- Interactive flame graphs with zoom
- Differential comparison (before/after)

**Why it matters:** HFT engineers live in microseconds. Show them you care about performance at their level.

---

## Technical Excellence Requirements

The target audience will scrutinize our technical choices. We must exceed their standards.

### Type Safety
- **PureScript frontend:** Stronger guarantees than TypeScript
- **Lean4 backend proofs:** Mathematical correctness
- **Row polymorphism:** API contracts verified at compile time
- **No runtime type errors:** Period.

### Performance
- **<50ms state update latency:** Benchmark-gated CI
- **<100ms UI response:** All interactions
- **<1s initial load:** Including WebSocket connection
- **Zero jank:** 60fps animations or no animations

### Keyboard-First
- **Full Vim bindings:** j/k, gg/G, /, etc.
- **Command palette:** Every action accessible via Ctrl+Shift+P
- **No mouse required:** Complete workflows without touching mouse
- **Focus discipline:** Browser never steals focus from terminal

### Security
- **OAuth device flow:** No embedded API keys
- **Keychain integration:** System credential storage
- **No telemetry:** Privacy by default
- **Audit logging:** All actions traceable

---

## Success Metrics

### Quantitative Targets

| Metric | Target | Measurement |
|--------|--------|-------------|
| State update latency | <50ms p99 | Continuous benchmark |
| User adoption | 30% of OpenCode users | Opt-in analytics |
| Cost savings | 15%+ reduction | User surveys |
| Proof usage | 20% of sessions | Feature flags |
| Session duration | >30min average | When sidepanel active |
| Terminal purist conversion | 10% try it | Marketing attribution |

### Qualitative Targets

| Signal | Indicator |
|--------|-----------|
| Technical respect | "I didn't know I wanted this" |
| Workflow integration | Users keep sidepanel open by default |
| Word of mouth | Engineers recommend to skeptical peers |
| Proof adoption | Users add theorem annotations unprompted |
| Performance appreciation | "Finally, someone who gets latency" |

---

## Competitive Positioning

### vs. Cursor IDE

| Aspect | Cursor | OpenCode Sidepanel |
|--------|--------|-------------------|
| Base | VSCode fork (Electron, heavy) | Terminal native (lightweight) |
| AI integration | Excellent | Excellent + Venice/Diem |
| Formal verification | None | Lean4 integration |
| Cost visibility | Basic dashboard | Real-time with countdown |
| Keyboard efficiency | Good | Superior (terminal native) |
| Resource usage | High (Electron) | Low (terminal + optional browser) |
| Time-travel | None | Full state history |

**Positioning:** "Cursor power, terminal efficiency, formal verification."

### vs. Claude Code

| Aspect | Claude Code | OpenCode Sidepanel |
|--------|-------------|-------------------|
| Provider | Anthropic only | Venice + multi-provider |
| GUI | None | Full browser sidepanel |
| Cost tracking | Basic | Diem countdown + projection |
| Proofs | None | Lean4 integration |
| Extensibility | Limited | Full plugin system |

**Positioning:** "Claude Code visualization, provider freedom, proof integration."

### vs. Raw Terminal + OpenCode

| Aspect | Raw OpenCode | With Sidepanel |
|--------|--------------|----------------|
| Token visibility | Text only | Charts + countdown |
| Cost awareness | End of session | Real-time |
| State inspection | Manual | Visual timeline |
| Proof integration | Manual setup | Integrated panel |
| Performance insight | None | Flame graphs |

**Positioning:** "Everything you love, plus everything you didn't know you needed."

---

## Implementation Phases

### Phase 1: Foundation (Weeks 1-4)
**Goal:** Working sidepanel with Diem tracking

Deliverables:
- Nix flake with all dependencies
- OpenCode plugin scaffold
- WebSocket bridge server
- PureScript/Halogen app shell
- Diem balance widget with countdown
- Basic terminal↔browser switching

Success criteria:
- User can see Diem balance update in real-time
- Countdown timer accurate to UTC midnight
- Plugin loads without breaking OpenCode

### Phase 2: Core Features (Weeks 5-10)
**Goal:** Full token tracking and terminal embedding

Deliverables:
- Comprehensive token usage dashboard
- Per-model cost breakdown
- Usage charts with time range selection
- Embedded terminal view (xterm.js)
- Session state persistence
- Command palette with Vim bindings

Success criteria:
- Complete cost visibility across all models
- Terminal embed functionally equivalent to native
- All actions accessible via keyboard

### Phase 3: Lean4 Integration (Weeks 11-16)
**Goal:** Proof-aware development workflow

Deliverables:
- lean-lsp-mcp configuration
- Proof status panel with goal display
- Tactic suggestions from LeanSearch
- Theorem library persistence
- Proof-aware code completion

Success criteria:
- Engineers can write and verify Lean4 proofs
- Goal state always visible and current
- Suggestions actually help close proofs

### Phase 4: Polish (Weeks 17-20)
**Goal:** Time-travel debugging and performance visualization

Deliverables:
- State snapshot system
- Visual timeline with scrubber
- Flame graph visualization
- Session recordings export
- Performance regression CI gates
- Documentation and demo videos

Success criteria:
- Can restore any previous state
- Flame graphs identify actual bottlenecks
- Demo videos make terminal purists curious

---

## Risks and Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Lean4 web ecosystem immature | High | Medium | Node.js proxy, avoid direct Lean4 HTTP |
| PureScript learning curve | Medium | Medium | Comprehensive docs, team training budget |
| OpenCode plugin API unstable | Medium | High | Abstract through adapter layer |
| Performance regression | Medium | High | Benchmark-gated CI, latency budgets |
| Scope creep | High | High | Strict phase gates, ship Phase 1 first |
| Venice API changes | Low | Medium | Version pinning, integration tests |

---

## Resource Requirements

### Team
- 1 senior full-stack engineer (PureScript + TypeScript)
- 1 Lean4 specialist (Phase 3 onward)
- 0.5 DevOps (Nix, CI/CD)
- 0.5 Design (terminal aesthetics, not traditional UI)

### Infrastructure
- Development: Local machines with Nix
- CI: GitHub Actions with Nix cache
- Staging: Single VPS for integration testing
- Production: User's local machine (sidepanel is local-first)

### Timeline
- Total: 20 weeks to feature-complete
- Phase 1: 4 weeks (MVP with Diem tracking)
- Phase 2: 6 weeks (full visualization)
- Phase 3: 6 weeks (Lean4 integration)
- Phase 4: 4 weeks (polish and time-travel)

---

## Decision Log

| Date | Decision | Rationale |
|------|----------|-----------|
| 2026-01-16 | PureScript over TypeScript | Type safety exceeds TS, impresses target audience |
| 2026-01-16 | Lean4 over Coq/Agda | Better tooling, Mathlib4 ecosystem, MCP exists |
| 2026-01-16 | Node.js bridge over Go | SDK is TypeScript, simpler integration |
| 2026-01-16 | WebSocket over HTTP polling | Real-time requirements, lower latency |
| 2026-01-16 | Nix Flakes over Docker | Reproducibility, declarative, matches target audience |
| 2026-01-16 | Venice primary over OpenAI/Anthropic | Diem economics, uncensored, differentiation |

---

## Appendices

### A. Glossary Reference
See `87-GLOSSARY.md` for term definitions.

### B. Architecture Diagrams
See `02-SYSTEM-ARCHITECTURE.md` for visual diagrams.

### C. Technology Deep Dive
See `03-TECHNOLOGY-STACK.md` for detailed rationale.

---

*"We're not building another IDE. We're building what senior engineers would build for themselves if they had time."*
