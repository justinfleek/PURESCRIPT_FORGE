# 87-GLOSSARY: Term Definitions

## A

### Aff
PureScript's asynchronous effect monad. Represents computations that may perform async operations (HTTP requests, timers, etc.) and may fail.

### Algebraic Data Type (ADT)
A composite type formed by combining other types using sum types (variants) or product types (records). Central to PureScript and Haskell programming.

### Alert Level
Status indicating balance urgency: `Normal`, `Warning`, `Critical`, or `Depleted`.

### Append-Only Log
Data structure where entries are only added, never modified or deleted. Used for session history to enable time-travel.

---

## B

### Balance
The combination of Diem and USD credits available for Venice API usage.

### Bridge Server
Node.js middleware that connects OpenCode (via plugin) to the browser (via WebSocket). Central coordination point.

### Bubbletea
Go library for building terminal user interfaces. Used by OpenCode for its TUI.

---

## C

### Component (Halogen)
A self-contained UI unit with its own state, actions, and rendering logic. Composable and type-safe.

### Consumption Rate
Rate at which Diem balance is being spent, measured in Diem per hour.

### Countdown
Time remaining until Diem reset at UTC midnight.

---

## D

### Diem
Venice AI's token-based credit system. 1 Diem = $1 of API credit. Resets daily at midnight UTC.

### Diem Reset
Daily event at 00:00:00 UTC when Diem balance is restored to the staked amount.

### Drift (Timer)
Cumulative error in timing caused by JavaScript's `setInterval` not being perfectly accurate. Requires correction for long-running timers.

---

## E

### Effect
PureScript type representing synchronous side effects. Used for DOM manipulation, reading refs, etc.

### Effective Balance
Total available credit: Diem + USD balance.

### Event Hook
OpenCode plugin system's mechanism for receiving notifications about session, message, and tool events.

### Event Sourcing
Pattern where state changes are stored as a sequence of events rather than current state. Enables time-travel.

---

## F

### Flame Graph
Visualization technique showing hierarchical timing data. Used for performance analysis.

### Formal Verification
Mathematical proof that code meets its specification. Provided by Lean4 integration.

---

## G

### Goal (Lean4)
A proof obligation that must be satisfied. Displayed as `⊢ proposition` in the proof panel.

### GUI
Graphical User Interface. The browser-based sidepanel.

---

## H

### Halogen
PureScript's type-safe UI framework. Similar in concept to React but with stronger guarantees.

### Hook (Halogen)
Reusable stateful logic extracted from components. Similar to React hooks.

---

## I

### Invariant
A property that must always be true. Proven using Lean4 theorems.

---

## J

### JSON-RPC 2.0
Protocol used for WebSocket communication between bridge and browser. Structured request/response with error handling.

---

## K

### Keybinding
Keyboard shortcut for an action. The sidepanel uses Vim-style bindings.

---

## L

### Lean4
Functional programming language and theorem prover. Used for formal verification.

### lean-lsp-mcp
MCP server that provides Lean4 language server functionality for agentic theorem proving.

### LSP
Language Server Protocol. Standard for IDE features like completions, diagnostics, and go-to-definition.

---

## M

### Mathlib4
Comprehensive mathematical library for Lean4. Provides foundations for proofs.

### MCP
Model Context Protocol. Anthropic's standard for connecting AI models to external tools.

### Monad
Abstract type representing sequential computation with effects. AppM, Aff, and Effect are monads.

---

## N

### Nix Flakes
Nix's modern way of managing packages and development environments. Provides reproducibility.

### Notification (JSON-RPC)
A message that doesn't expect a response. Used for server-to-client state updates.

---

## O

### OpenCode
Terminal-based AI coding assistant. The host application for the sidepanel plugin.

---

## P

### Phase
A major milestone in the implementation roadmap. Four phases total.

### Plugin
OpenCode extension that receives events and can modify behavior. The sidepanel is implemented as a plugin.

### Proof Status
Current state of Lean4 verification: goals, diagnostics, context.

### PureScript
Strongly-typed functional programming language that compiles to JavaScript.

### PTY
Pseudo-terminal. Used for terminal emulation in the browser.

---

## Q

### Query (Halogen)
Message sent from parent to child component to request data or trigger actions.

---

## R

### Rate Limit
Maximum requests or tokens per time period. Venice has tier-based limits.

### Reducer
Pure function that takes current state and an action, returning new state.

### Row Polymorphism
Type system feature allowing functions to work with records having at least certain fields. Stronger than TypeScript's structural typing.

---

## S

### Session
A continuous interaction with the AI assistant. Tracks messages, tokens, and cost.

### Sidepanel
The browser-based GUI that extends OpenCode with visual features.

### Snapshot
Saved point-in-time state for time-travel debugging.

### Slot (Halogen)
Type-safe reference to a child component, enabling parent-child communication.

### Spago
PureScript package manager and build tool.

### SSE
Server-Sent Events. One-way streaming from server to client. Used by Venice for streaming responses.

### State Synchronization
Process of keeping TUI and browser state consistent.

### Subscription (Halogen)
Long-running process that emits actions to a component. Used for timers, WebSocket messages.

---

## T

### Tactic (Lean4)
A command that transforms the proof state. Examples: `simp`, `rfl`, `induction`.

### Terminal Apostasy
Project codename. Refers to converting terminal purists to GUI usage.

### Theorem
A proven mathematical statement. Stored in the theorem library.

### Theorem Library
Persistent collection of verified theorems for reuse.

### Tier (Venice)
Model pricing category: XS, S, M, L. Different costs and rate limits.

### Time-Travel Debugging
Ability to restore previous states and understand what changed.

### TUI
Terminal User Interface. OpenCode's primary interface.

---

## U

### Urgency Level
See Alert Level.

### Usage
Token consumption metrics: prompt tokens, completion tokens, cost.

### UTC
Coordinated Universal Time. Diem resets at UTC midnight.

---

## V

### Venice AI
AI inference provider with Diem token economics.

### VVV
Venice's token that can be staked to earn Diem allocation.

### Vibe Coding
Informal, intuitive coding approach assisted by AI. What terminal purists skeptically view.

---

## W

### WebSocket
Bidirectional communication protocol. Used between bridge and browser.

### Widget
UI component displaying a specific piece of information. DiemTracker is a widget.

---

## X

### xterm.js
JavaScript terminal emulator. Used to embed terminal view in browser.

---

## Symbols

### ⊢ (Turnstile)
Lean4 symbol meaning "proves" or "it follows that". Appears before goals.

### → (Arrow)
Function type in PureScript/Lean4. `A → B` means function from A to B.

### ∀ (For All)
Universal quantifier. "For all values of..."

### ≤ (Less Than or Equal)
Comparison operator used in proofs.

---

## Acronyms

| Acronym | Expansion |
|---------|-----------|
| ADT | Algebraic Data Type |
| API | Application Programming Interface |
| CI/CD | Continuous Integration/Continuous Deployment |
| CSS | Cascading Style Sheets |
| DOM | Document Object Model |
| FFI | Foreign Function Interface |
| GUI | Graphical User Interface |
| HFT | High-Frequency Trading |
| HTTP | Hypertext Transfer Protocol |
| JSON | JavaScript Object Notation |
| LSP | Language Server Protocol |
| MCP | Model Context Protocol |
| MVP | Minimum Viable Product |
| PTY | Pseudo-Terminal |
| RPC | Remote Procedure Call |
| SDK | Software Development Kit |
| SPA | Single Page Application |
| SSE | Server-Sent Events |
| TLS | Transport Layer Security |
| TUI | Terminal User Interface |
| UI | User Interface |
| UTC | Coordinated Universal Time |
| UX | User Experience |
| VVV | Venice Value Token |
| WS | WebSocket |

---

*"If you can't explain it simply, you don't understand it well enough." — Einstein*
