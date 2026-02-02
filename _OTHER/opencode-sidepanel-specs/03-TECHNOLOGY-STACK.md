# 03-TECHNOLOGY-STACK: All Technology Choices with Rationale

## Stack Summary

| Layer | Technology | Version | Purpose |
|-------|------------|---------|---------|
| Backend Proofs | Lean4 | 4.x | Formal verification |
| Frontend | PureScript + Halogen | 0.15.x | Type-safe UI |
| Bridge Server | Node.js + TypeScript | 20 LTS | Coordination layer |
| TUI Extension | Go + Bubbletea | (OpenCode native) | Plugin integration |
| Real-time | WebSocket + JSON-RPC | 2.0 | State synchronization |
| AI Provider | Venice AI | v1 | Primary inference |
| MCP Server | lean-lsp-mcp | latest | Theorem proving |
| Build System | Nix Flakes | 2.18+ | Reproducibility |
| Package Manager | pnpm (Node) / Spago (PS) | 8.x / 0.21.x | Dependencies |
| Terminal Embed | xterm.js | 5.x | Browser terminal |
| Charts | Recharts | 2.x | Data visualization |
| Testing | Vitest (TS) / purescript-spec | latest | Test frameworks |

---

## Frontend: PureScript + Halogen

### What is PureScript?
PureScript is a strongly-typed functional programming language that compiles to JavaScript. It's essentially Haskell for the browser, with some practical improvements for web development.

### Why PureScript over TypeScript?

| Aspect | TypeScript | PureScript | Winner |
|--------|------------|------------|--------|
| Type safety | Structural, escapable | Strict, enforced | PureScript |
| Runtime errors | Common (any, casting) | Extremely rare | PureScript |
| Row polymorphism | Limited | Full support | PureScript |
| Effect tracking | None | Required (Effect/Aff) | PureScript |
| Bundle size | Varies | Predictable | Tie |
| Hiring | Easy | Difficult | TypeScript |
| Target audience appeal | Standard | Impressive | PureScript |

**The key insight:** Our target audience (ex-FAANG, HFT) will scrutinize technology choices. PureScript signals technical seriousness in a way TypeScript cannot.

### Why Halogen over React/Elm?

**vs. React:**
- React requires discipline to avoid runtime errors
- PureScript-React bindings are second-class
- Halogen is native PureScript, fully type-safe

**vs. Elm:**
- Elm is its own language ecosystem
- Halogen integrates with PureScript ecosystem
- Halogen supports more advanced patterns (subscriptions, forking)

### Halogen Key Concepts

```purescript
-- Component structure
component :: forall q i o m. MonadAff m => H.Component q i o m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval { handleAction = handleAction }
  }

-- State is explicitly typed
type State = { balance :: Number, countdown :: Duration }

-- Actions are algebraic data types (exhaustive matching required)
data Action = Tick | UpdateBalance Number | ResetCountdown

-- Effects are tracked in the type system
handleAction :: forall o m. MonadAff m => Action -> H.HalogenM State Action () o m Unit
```

### PureScript Libraries We'll Use

| Library | Purpose | Import |
|---------|---------|--------|
| halogen | UI framework | `import Halogen as H` |
| halogen-hooks | React-style hooks | `import Halogen.Hooks as Hooks` |
| aff | Async effects | `import Effect.Aff` |
| affjax | HTTP client | `import Affjax` |
| argonaut | JSON handling | `import Data.Argonaut` |
| routing | SPA routing | `import Routing.Hash` |
| datetime | Time handling | `import Data.DateTime` |
| css | Styling | `import Halogen.HTML.CSS` |

### Bundle Size Target
- Initial load: < 200KB gzipped
- Includes: Halogen runtime, all components, charting
- Strategy: Code splitting by route (Phase 2)

---

## Bridge Server: Node.js + TypeScript

### Why Node.js?

1. **SDK Compatibility:** @opencode-ai/sdk is TypeScript
2. **WebSocket Maturity:** `ws` library is battle-tested
3. **Async Model:** Event loop handles concurrent connections well
4. **Team Familiarity:** Most engineers know Node.js
5. **Deployment:** Single binary possible via `pkg`

### Why Not Go/Rust for Bridge?

**vs. Go:**
- Would require FFI to use TypeScript SDK
- Or rewriting SDK bindings (unnecessary work)
- Performance difference negligible at our scale

**vs. Rust:**
- Same FFI issues
- Overkill for coordination layer
- Bridge is I/O bound, not CPU bound

### Node.js Dependencies

```json
{
  "dependencies": {
    "@opencode-ai/sdk": "^0.x",
    "ws": "^8.x",
    "better-sqlite3": "^9.x",
    "zod": "^3.x",
    "pino": "^8.x"
  },
  "devDependencies": {
    "typescript": "^5.x",
    "vitest": "^1.x",
    "tsx": "^4.x"
  }
}
```

### Bridge Server Architecture

```typescript
// Main entry point structure
import { OpenCodeClient } from '@opencode-ai/sdk';
import { WebSocketServer } from 'ws';
import { createVeniceProxy } from './venice-proxy';
import { createLeanProxy } from './lean-proxy';
import { createSessionStore } from './session-store';

async function main() {
  const opencode = new OpenCodeClient();
  const wss = new WebSocketServer({ port: 8765 });
  const venice = createVeniceProxy();
  const lean = createLeanProxy();
  const sessions = createSessionStore();
  
  // Wire up event flows
  opencode.on('session.updated', (data) => {
    sessions.append(data);
    broadcast(wss, { type: 'session', data });
  });
  
  // ... etc
}
```

---

## Formal Verification: Lean4

### Why Lean4?

1. **Active Development:** Lean4 is modern, actively maintained
2. **Mathlib4:** Massive mathematical library
3. **MCP Exists:** lean-lsp-mcp provides agentic access
4. **Type Theory:** Dependent types enable powerful proofs
5. **Compilation:** Can compile to efficient C code (future use)

### Why Not Coq/Agda/Idris?

| Proof Assistant | Maturity | Tooling | MCP Support | Choice |
|-----------------|----------|---------|-------------|--------|
| Lean4 | Modern | Excellent | Yes | ✓ |
| Coq | Mature | Good | No | |
| Agda | Academic | Limited | No | |
| Idris2 | Experimental | Limited | No | |

### lean-lsp-mcp Tools

The MCP server provides these tools for agentic theorem proving:

```
lean_goal            - Get proof goals at cursor
lean_term_goal       - Get goal for specific term
lean_hover_info      - Type information on hover
lean_diagnostic_messages - Errors and warnings
lean_references      - Find all references
lean_completions     - Term/tactic completions
lean_run_code        - Execute Lean code
lean_multi_attempt   - Try multiple tactics
```

### Example Proof Integration

```lean
-- User writes in editor
theorem diem_balance_non_negative (account : Account) : 
    account.diemBalance ≥ 0 := by
  -- Sidepanel shows: ⊢ account.diemBalance ≥ 0
  -- Tactic suggestions: exact account.balance_invariant
  exact account.balance_invariant

-- On success, sidepanel shows: ✓ Proof complete
```

### Mathlib4 Integration

We'll use Mathlib4 for:
- Number theory (token calculations)
- Order theory (state monotonicity)
- Logic foundations (invariant proofs)

```lean
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

-- Example: Proving session token counts are monotonic
theorem session_tokens_monotonic (s₁ s₂ : Session) 
    (h : s₁.timestamp < s₂.timestamp) :
    s₁.totalTokens ≤ s₂.totalTokens := by
  -- Use Mathlib's order theory
  exact Session.monotonic_tokens h
```

---

## AI Provider: Venice AI

### Why Venice Over OpenAI/Anthropic?

| Aspect | Venice | OpenAI | Anthropic |
|--------|--------|--------|-----------|
| Diem economics | ✓ Unique | Pay-per-token | Pay-per-token |
| Uncensored | ✓ Yes | Filtered | Filtered |
| Privacy | ✓ No data retention | Logged | Logged |
| Cost tracking | ✓ Response headers | Separate API | Separate API |
| Differentiator | ✓ Strong | Commodity | Commodity |

### Venice API Integration Points

```typescript
// Response header extraction (after every request)
const balance = {
  diem: parseFloat(response.headers.get('x-venice-balance-diem') ?? '0'),
  usd: parseFloat(response.headers.get('x-venice-balance-usd') ?? '0'),
  remainingTokens: parseInt(response.headers.get('x-ratelimit-remaining-tokens') ?? '0'),
  remainingRequests: parseInt(response.headers.get('x-ratelimit-remaining-requests') ?? '0')
};
```

### Venice Model Tiers

| Tier | Models | Input $/M | Output $/M | RPM | TPM |
|------|--------|-----------|------------|-----|-----|
| XS | qwen3-4b | $0.10 | $0.10 | 500 | 1M |
| S | llama-3.2-3b | $0.20 | $0.20 | 200 | 1M |
| M | llama-3.3-70b | $0.30 | $0.60 | 50 | 750K |
| L | deepseek-r1 | $0.50 | $2.00 | 20 | 500K |

### Multi-Provider Future

While Venice is primary, architecture supports adding:
- Anthropic (Claude)
- OpenAI (GPT)
- Local models (Ollama)

Provider interface:
```typescript
interface AIProvider {
  name: string;
  chat(messages: Message[]): AsyncIterable<Chunk>;
  getBalance(): Promise<Balance | null>;
  getRateLimits(): Promise<RateLimits>;
}
```

---

## Build System: Nix Flakes

### Why Nix?

1. **Reproducibility:** Same build everywhere, forever
2. **Target Audience:** Senior engineers love Nix
3. **Dependency Hell:** Nix eliminates it
4. **Development Shells:** Instant environment setup
5. **Cross-Platform:** macOS, Linux, WSL2

### Flake Structure

```nix
{
  description = "OpenCode Sidepanel";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    purescript-overlay.url = "github:thomashoneyman/purescript-overlay";
    lean4.url = "github:leanprover/lean4";
  };

  outputs = { self, nixpkgs, flake-utils, purescript-overlay, lean4 }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ purescript-overlay.overlays.default ];
        };
      in {
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            # Node.js
            nodejs_20
            pnpm
            
            # PureScript
            purescript
            spago-unstable
            purs-tidy
            
            # Lean4
            lean4.packages.${system}.lean
            
            # Tools
            just
            watchexec
          ];
        };

        packages.default = pkgs.buildNpmPackage {
          pname = "opencode-sidepanel";
          version = "0.1.0";
          src = ./.;
          # ... build configuration
        };
      }
    );
}
```

### Development Commands

```bash
# Enter development shell
nix develop

# Build everything
just build

# Run development server
just dev

# Run tests
just test

# Format code
just fmt
```

---

## Terminal Embedding: xterm.js

### Why xterm.js?

1. **Industry Standard:** Used by VSCode, Hyper, etc.
2. **Performance:** GPU-accelerated rendering
3. **Compatibility:** Full terminal emulation
4. **Addons:** WebLinks, fit, search, etc.

### Integration Pattern

```typescript
// PureScript FFI to xterm.js
foreign import createTerminal :: Effect Terminal
foreign import writeTerminal :: Terminal -> String -> Effect Unit
foreign import onData :: Terminal -> (String -> Effect Unit) -> Effect Unit

-- Halogen component wrapping xterm
terminalEmbed :: forall q i o m. MonadAff m => H.Component q i o m
terminalEmbed = H.mkComponent { ... }
```

### Terminal↔TUI Communication

```
Browser xterm.js ──── WebSocket ────► Bridge ──── PTY ────► OpenCode TUI
     (render)         (transport)     (relay)    (data)      (source)
```

---

## Data Visualization: Recharts

### Why Recharts?

1. **React-Compatible:** Works with PureScript-React interop
2. **Declarative:** Fits functional style
3. **Responsive:** Handles resize gracefully
4. **Customizable:** Full control over styling

### Chart Types We'll Use

| Chart | Use Case | Component |
|-------|----------|-----------|
| LineChart | Token usage over time | `<TokenUsageChart />` |
| AreaChart | Cost accumulation | `<CostChart />` |
| BarChart | Model comparison | `<ModelUsageChart />` |
| PieChart | Session breakdown | `<SessionPieChart />` |

### Performance Considerations

- **Data windowing:** Only render visible points
- **Debounced updates:** Batch rapid changes
- **Canvas fallback:** For large datasets

---

## Testing Strategy

### Unit Testing

| Layer | Framework | Purpose |
|-------|-----------|---------|
| PureScript | purescript-spec | Component logic |
| TypeScript | Vitest | Bridge server |
| Lean4 | Built-in | Proof verification |

### Integration Testing

```typescript
// Vitest integration test example
describe('Venice Balance Tracking', () => {
  it('extracts balance from response headers', async () => {
    const mockResponse = new Response('{}', {
      headers: {
        'x-venice-balance-diem': '42.5',
        'x-venice-balance-usd': '10.00'
      }
    });
    
    const balance = extractBalance(mockResponse);
    
    expect(balance.diem).toBe(42.5);
    expect(balance.usd).toBe(10.0);
  });
});
```

### Property Testing

```purescript
-- QuickCheck-style property test
prop_countdown_never_negative :: DateTime -> Boolean
prop_countdown_never_negative now =
  let countdown = timeUntilReset now
  in countdown >= Duration.zero
```

---

## Security Libraries

| Purpose | Library | Usage |
|---------|---------|-------|
| Secrets storage | keytar | macOS Keychain, Linux Secret Service |
| JWT validation | jose | Token verification |
| Input sanitization | DOMPurify | XSS prevention |
| HTTPS | Node built-in | TLS for external calls |

---

## Performance Monitoring

| Metric | Tool | Target |
|--------|------|--------|
| State update latency | Custom timing | < 50ms |
| Bundle size | bundlewatch | < 200KB |
| Memory usage | Chrome DevTools | < 100MB |
| WebSocket latency | Custom | < 10ms |

---

## Version Pinning Strategy

All dependencies pinned to exact versions in:
- `package.json` (Node.js)
- `spago.yaml` (PureScript)
- `flake.lock` (Nix)

Update process:
1. Create branch `deps/update-YYYY-MM`
2. Run `nix flake update`
3. Run `pnpm update`
4. Run full test suite
5. Review changelogs for breaking changes
6. Merge only if all tests pass

---

## Technology Decision Log

| Date | Decision | Alternatives Considered | Rationale |
|------|----------|------------------------|-----------|
| 2026-01-16 | PureScript | TypeScript, Elm | Type safety impresses target audience |
| 2026-01-16 | Halogen | React, purescript-react | Native PureScript, full type safety |
| 2026-01-16 | Node.js | Go, Rust, Deno | SDK compatibility, team familiarity |
| 2026-01-16 | Lean4 | Coq, Agda | MCP support, active development |
| 2026-01-16 | Venice | OpenAI, Anthropic | Diem economics, differentiation |
| 2026-01-16 | Nix Flakes | Docker, asdf | Reproducibility, target audience appeal |
| 2026-01-16 | xterm.js | Terminal.js, none | Industry standard, performance |
| 2026-01-16 | Recharts | D3 direct, Chart.js | Declarative, React-compatible |
| 2026-01-16 | WebSocket | SSE, polling | Bidirectional, low latency |

---

*"Choose boring technology... unless your audience is impressed by exciting technology. Then choose exciting technology that's actually stable."*
