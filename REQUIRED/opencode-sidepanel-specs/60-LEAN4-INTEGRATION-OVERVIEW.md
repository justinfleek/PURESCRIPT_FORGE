# 60-LEAN4-INTEGRATION-OVERVIEW: Formal Verification for the Skeptical Engineer

## Overview

Lean4 integration is the Phase 3 crown jewel—a feature that transforms the sidepanel from a "nice monitoring dashboard" into something that genuinely earns the respect of formal methods enthusiasts. This document covers the integration architecture, MCP tools, and use cases.

---

## Why Lean4?

### For the Target User

Senior engineers who've worked on mission-critical systems understand that tests can only prove the presence of bugs, not their absence. Formal verification provides mathematical certainty:

- **Correct by construction** - Prove your invariants hold before deploying
- **Catch corner cases** - The type checker explores all code paths
- **Document intent** - Types are executable specifications
- **Impress skeptics** - "We formally verify our state transitions" ends debates

### Why Lean4 Specifically?

| Feature | Lean4 | Coq | Agda | Idris2 |
|---------|-------|-----|------|--------|
| MCP Server | ✅ lean-lsp-mcp | ❌ | ❌ | ❌ |
| Active Development | ✅ Very active | ⚠️ Stable | ⚠️ Academic | ⚠️ Small team |
| Mathlib | ✅ Mathlib4 | ✅ MathComp | ⚠️ Limited | ❌ |
| Compiles to Native | ✅ C via Lake | ⚠️ Extraction | ⚠️ | ✅ Chez |
| Learning Resources | ✅ Growing | ✅ Mature | ⚠️ | ⚠️ |

The existence of `lean-lsp-mcp` is the deciding factor—it provides tool access to proof state that we can surface in the sidepanel.

---

## Architecture

### Integration Points

```
┌───────────────────────────────────────────────────────────────────────┐
│                           SIDEPANEL                                   │
│                                                                        │
│  ┌────────────────────────────────────────────────────────────────┐   │
│  │                    PROOF STATUS PANEL                          │   │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐  │   │
│  │  │ Goal Display │  │   Context    │  │ Tactic Suggestions   │  │   │
│  │  │              │  │   Variables  │  │                      │  │   │
│  │  │  ⊢ P → Q     │  │  h : P      │  │  • exact h           │  │   │
│  │  │              │  │  p : Nat    │  │  • apply And.intro   │  │   │
│  │  └──────────────┘  └──────────────┘  └──────────────────────┘  │   │
│  └────────────────────────────────────────────────────────────────┘   │
│                                │                                       │
│                                │ WebSocket                             │
│                                ▼                                       │
│  ┌────────────────────────────────────────────────────────────────┐   │
│  │                       BRIDGE SERVER                            │   │
│  │                                                                 │   │
│  │  ┌─────────────────────────────────────────────────────────┐   │   │
│  │  │                    LEAN PROXY                            │   │   │
│  │  │  • Forwards MCP tool calls                              │   │   │
│  │  │  • Caches recent proof state                            │   │   │
│  │  │  • Debounces rapid file changes                         │   │   │
│  │  │  • Parses and structures responses                      │   │   │
│  │  └─────────────────────────────────────────────────────────┘   │   │
│  │                                │                                │   │
│  └────────────────────────────────┼────────────────────────────────┘   │
│                                   │ MCP Protocol                       │
└───────────────────────────────────┼───────────────────────────────────┘
                                    ▼
                          ┌─────────────────────┐
                          │    lean-lsp-mcp     │
                          │                     │
                          │  Lean4 LSP Server   │
                          │  • lean_goal        │
                          │  • lean_term_goal   │
                          │  • lean_hover_info  │
                          │  • lean_diagnostics │
                          │  • lean_completions │
                          └─────────────────────┘
                                    │
                                    ▼
                          ┌─────────────────────┐
                          │    Lean4 Project    │
                          │                     │
                          │  *.lean files       │
                          │  lakefile.lean      │
                          │  lean-toolchain     │
                          └─────────────────────┘
```

### Data Flow: File Edit → Goal Display

```
1. User edits .lean file in editor
        │
        ▼
2. OpenCode plugin detects file.write event
        │
        │  event: { type: 'file.write', path: '/src/Theorem.lean' }
        ▼
3. Bridge receives event, checks if .lean file
        │
        │  if (path.endsWith('.lean')) triggerProofCheck(path)
        ▼
4. Bridge calls lean-lsp-mcp via MCP
        │
        │  tool: 'lean_goal', params: { file, line, column }
        ▼
5. lean-lsp-mcp queries Lean4 LSP
        │
        │  LSP: textDocument/hover, textDocument/diagnostic
        ▼
6. Response parsed and structured
        │
        │  { goals: [...], diagnostics: [...], context: [...] }
        ▼
7. Bridge broadcasts via WebSocket
        │
        │  notification: 'proof.update', params: { ... }
        ▼
8. Browser receives, updates ProofPanel component
        │
        ▼
9. User sees current proof state in sidepanel
```

---

## MCP Tools Reference

### lean_goal

Get the current proof goal at a position.

**Request:**
```json
{
  "method": "tool/call",
  "params": {
    "name": "lean_goal",
    "arguments": {
      "file": "/path/to/file.lean",
      "line": 42,
      "column": 10
    }
  }
}
```

**Response:**
```json
{
  "goals": [
    {
      "case": "",
      "hypotheses": [
        { "name": "h", "type": "P", "value": null },
        { "name": "n", "type": "Nat", "value": "5" }
      ],
      "conclusion": "Q"
    }
  ]
}
```

**Display Format:**
```
h : P
n : Nat := 5
⊢ Q
```

### lean_term_goal

Get type information for a term.

**Request:**
```json
{
  "method": "tool/call",
  "params": {
    "name": "lean_term_goal",
    "arguments": {
      "file": "/path/to/file.lean",
      "line": 42,
      "column": 10
    }
  }
}
```

**Response:**
```json
{
  "type": "Nat → Nat → Nat",
  "expectedType": "Nat → Nat → Nat"
}
```

### lean_hover_info

Get documentation and type at hover position.

**Request:**
```json
{
  "method": "tool/call", 
  "params": {
    "name": "lean_hover_info",
    "arguments": {
      "file": "/path/to/file.lean",
      "line": 42,
      "column": 10
    }
  }
}
```

**Response:**
```json
{
  "contents": {
    "kind": "markdown",
    "value": "```lean\ndef List.map : (α → β) → List α → List β\n```\n\nApply a function to each element of a list."
  }
}
```

### lean_diagnostic_messages

Get all diagnostics (errors, warnings) for a file.

**Request:**
```json
{
  "method": "tool/call",
  "params": {
    "name": "lean_diagnostic_messages",
    "arguments": {
      "file": "/path/to/file.lean"
    }
  }
}
```

**Response:**
```json
{
  "diagnostics": [
    {
      "range": {
        "start": { "line": 10, "character": 4 },
        "end": { "line": 10, "character": 15 }
      },
      "severity": 1,
      "message": "type mismatch\n  h\nhas type\n  P\nbut is expected to have type\n  Q"
    }
  ]
}
```

### lean_completions

Get tactic/term completions at position.

**Request:**
```json
{
  "method": "tool/call",
  "params": {
    "name": "lean_completions",
    "arguments": {
      "file": "/path/to/file.lean",
      "line": 42,
      "column": 10
    }
  }
}
```

**Response:**
```json
{
  "completions": [
    { "label": "exact", "kind": "tactic", "detail": "Provide exact proof term" },
    { "label": "apply", "kind": "tactic", "detail": "Apply a lemma" },
    { "label": "simp", "kind": "tactic", "detail": "Simplify using simp lemmas" },
    { "label": "rfl", "kind": "tactic", "detail": "Reflexivity" }
  ]
}
```

### lean_references

Find all references to a symbol.

**Request:**
```json
{
  "method": "tool/call",
  "params": {
    "name": "lean_references",
    "arguments": {
      "file": "/path/to/file.lean",
      "line": 42,
      "column": 10
    }
  }
}
```

### lean_run_code

Execute Lean code and return output.

**Request:**
```json
{
  "method": "tool/call",
  "params": {
    "name": "lean_run_code",
    "arguments": {
      "code": "#check Nat.add_comm"
    }
  }
}
```

**Response:**
```json
{
  "output": "Nat.add_comm : ∀ (n m : Nat), n + m = m + n"
}
```

---

## Bridge Lean Proxy Implementation

```typescript
// src/lean/proxy.ts
import { MCPClient } from '@modelcontextprotocol/sdk/client';
import { debounce } from 'lodash';

interface ProofState {
  file: string;
  position: { line: number; column: number };
  goals: ProofGoal[];
  diagnostics: Diagnostic[];
  context: ContextVariable[];
  suggestedTactics: TacticSuggestion[];
}

interface ProofGoal {
  case: string;
  hypotheses: Array<{ name: string; type: string; value?: string }>;
  conclusion: string;
}

export class LeanProxy {
  private mcp: MCPClient;
  private store: StateStore;
  private connected: boolean = false;
  private cache: Map<string, ProofState> = new Map();
  
  constructor(store: StateStore) {
    this.store = store;
    this.mcp = new MCPClient();
    
    // Debounce proof checks to avoid hammering LSP
    this.checkProof = debounce(this.checkProofImpl.bind(this), 300, {
      leading: true,
      trailing: true
    });
  }
  
  async connect(config: LeanConfig): Promise<void> {
    try {
      await this.mcp.connect({
        command: config.command,
        args: config.args,
        transport: 'stdio'
      });
      
      this.connected = true;
      this.store.updateProof({ connected: true });
      
      logger.info('Lean LSP connected');
    } catch (error) {
      this.connected = false;
      this.store.updateProof({ connected: false });
      logger.error('Failed to connect to Lean LSP', { error });
      // Don't throw - we can function without Lean
    }
  }
  
  checkProof: (file: string, line: number, column: number) => void;
  
  private async checkProofImpl(file: string, line: number, column: number): Promise<void> {
    if (!this.connected) return;
    
    try {
      // Fetch all proof-related data in parallel
      const [goals, diagnostics, completions] = await Promise.all([
        this.getGoals(file, line, column),
        this.getDiagnostics(file),
        this.getCompletions(file, line, column)
      ]);
      
      const proofState: ProofState = {
        file,
        position: { line, column },
        goals: goals,
        diagnostics: diagnostics,
        context: this.extractContext(goals),
        suggestedTactics: this.rankTactics(completions, goals)
      };
      
      // Cache for quick access
      const cacheKey = `${file}:${line}:${column}`;
      this.cache.set(cacheKey, proofState);
      
      // Update store (triggers broadcast to browser)
      this.store.updateProof({
        currentFile: file,
        goals: proofState.goals,
        diagnostics: proofState.diagnostics,
        suggestedTactics: proofState.suggestedTactics
      });
      
    } catch (error) {
      logger.error('Failed to check proof', { file, line, column, error });
      // Don't update store on error - keep last known state
    }
  }
  
  private async getGoals(file: string, line: number, column: number): Promise<ProofGoal[]> {
    const result = await this.mcp.callTool('lean_goal', { file, line, column });
    return this.parseGoals(result);
  }
  
  private async getDiagnostics(file: string): Promise<Diagnostic[]> {
    const result = await this.mcp.callTool('lean_diagnostic_messages', { file });
    return this.parseDiagnostics(result);
  }
  
  private async getCompletions(file: string, line: number, column: number): Promise<Completion[]> {
    const result = await this.mcp.callTool('lean_completions', { file, line, column });
    return this.parseCompletions(result);
  }
  
  private parseGoals(result: unknown): ProofGoal[] {
    // Parse MCP response into structured goals
    // Handle various Lean4 goal formats
    if (!result || typeof result !== 'object') return [];
    
    const data = result as { goals?: unknown[] };
    if (!Array.isArray(data.goals)) return [];
    
    return data.goals.map(goal => ({
      case: (goal as any).case ?? '',
      hypotheses: this.parseHypotheses((goal as any).hypotheses),
      conclusion: (goal as any).conclusion ?? ''
    }));
  }
  
  private parseHypotheses(hyps: unknown): Array<{ name: string; type: string; value?: string }> {
    if (!Array.isArray(hyps)) return [];
    
    return hyps.map(h => ({
      name: (h as any).name ?? '',
      type: (h as any).type ?? '',
      value: (h as any).value
    }));
  }
  
  private extractContext(goals: ProofGoal[]): ContextVariable[] {
    // Flatten all hypotheses from all goals into context
    const seen = new Set<string>();
    const context: ContextVariable[] = [];
    
    for (const goal of goals) {
      for (const hyp of goal.hypotheses) {
        if (!seen.has(hyp.name)) {
          seen.add(hyp.name);
          context.push({
            name: hyp.name,
            type: hyp.type,
            value: hyp.value
          });
        }
      }
    }
    
    return context;
  }
  
  private rankTactics(completions: Completion[], goals: ProofGoal[]): TacticSuggestion[] {
    // Filter to tactics only
    const tactics = completions.filter(c => c.kind === 'tactic');
    
    // Rank based on goal structure
    // - `exact` if we have a matching hypothesis
    // - `rfl` if goal is equality
    // - `simp` generally useful
    // - etc.
    
    const ranked = tactics.map(tactic => ({
      name: tactic.label,
      description: tactic.detail,
      relevance: this.scoreTactic(tactic.label, goals)
    }));
    
    // Sort by relevance descending
    ranked.sort((a, b) => b.relevance - a.relevance);
    
    return ranked.slice(0, 10); // Top 10
  }
  
  private scoreTactic(name: string, goals: ProofGoal[]): number {
    const goal = goals[0];
    if (!goal) return 0;
    
    // Heuristic scoring
    switch (name) {
      case 'exact':
        // High score if hypothesis type matches conclusion
        return goal.hypotheses.some(h => h.type === goal.conclusion) ? 100 : 20;
      
      case 'rfl':
        // High score for equality goals
        return goal.conclusion.includes(' = ') ? 90 : 10;
      
      case 'simp':
        // Generally useful
        return 50;
      
      case 'apply':
        // Useful for implications
        return goal.conclusion.includes('→') ? 70 : 40;
      
      case 'intro':
        // Useful for foralls and implications
        return (goal.conclusion.includes('∀') || goal.conclusion.includes('→')) ? 80 : 30;
      
      case 'cases':
      case 'induction':
        // Useful when we have sum types or Nat
        return goal.hypotheses.some(h => h.type.includes('∨') || h.type === 'Nat') ? 60 : 20;
      
      default:
        return 10;
    }
  }
}
```

---

## Use Cases

### Use Case 1: Real-time Proof Assistance

**Scenario:** User is writing a theorem in Lean4 and wants to see the current goal state.

**Flow:**
1. User positions cursor after `by` in proof
2. Sidepanel shows current goal: `⊢ n + 0 = n`
3. Tactic suggestions show `simp`, `rfl` with high relevance
4. User types `simp` - goal closes
5. Sidepanel shows "No goals remaining ✓"

### Use Case 2: Error Diagnosis

**Scenario:** User has a type error and wants to understand it.

**Flow:**
1. User saves file with type error
2. Sidepanel diagnostics panel shows:
   ```
   Line 42: type mismatch
     h
   has type
     P
   but is expected to have type
     Q
   ```
3. Click on error → jumps to location (via OpenCode)

### Use Case 3: Theorem Discovery

**Scenario:** User needs a lemma about list concatenation.

**Flow:**
1. User opens Theorem Library panel
2. Types "list append" in search
3. Results show:
   - `List.append_assoc : (a ++ b) ++ c = a ++ (b ++ c)`
   - `List.append_nil : a ++ [] = a`
   - `List.nil_append : [] ++ a = a`
4. Click to insert theorem name at cursor

---

## Proof State Types (PureScript)

```purescript
module Sidepanel.State.Proof where

import Data.Maybe (Maybe)
import Data.Array (Array)

type ProofState =
  { connected :: Boolean
  , currentFile :: Maybe String
  , position :: Maybe Position
  , goals :: Array ProofGoal
  , diagnostics :: Array Diagnostic
  , suggestedTactics :: Array TacticSuggestion
  , theoremLibrary :: Array Theorem
  }

type Position = { line :: Int, column :: Int }

type ProofGoal =
  { case :: String
  , hypotheses :: Array Hypothesis
  , conclusion :: String
  }

type Hypothesis =
  { name :: String
  , type :: String
  , value :: Maybe String  -- for let-bound variables
  }

type Diagnostic =
  { range :: Range
  , severity :: DiagnosticSeverity
  , message :: String
  , source :: String
  }

data DiagnosticSeverity = Error | Warning | Information | Hint

type TacticSuggestion =
  { name :: String
  , description :: String
  , relevance :: Number  -- 0-100
  }

type Theorem =
  { name :: String
  , type :: String
  , docstring :: Maybe String
  , file :: String
  , verified :: Boolean
  }
```

---

## Configuration

### OpenCode MCP Configuration

```json
{
  "mcp": {
    "lean-lsp": {
      "type": "local",
      "command": "lean-lsp-mcp",
      "args": ["--transport", "stdio"],
      "env": {
        "LEAN_PATH": "/path/to/mathlib4/build/lib"
      }
    }
  }
}
```

### Nix Flake Lean4 Setup

```nix
{
  inputs.lean4.url = "github:leanprover/lean4/v4.5.0";
  
  outputs = { self, nixpkgs, lean4 }: {
    devShells.default = pkgs.mkShell {
      buildInputs = [
        lean4.packages.${system}.lean
        lean4.packages.${system}.lake
        # lean-lsp-mcp from our own package
      ];
    };
  };
}
```

---

## Performance Considerations

### Debouncing

Lean4 LSP can be slow on large files. We debounce proof checks:
- Wait 300ms after last keystroke before checking
- Cancel pending checks if new edit arrives
- Show "Checking..." indicator during LSP call

### Caching

Cache proof state by `file:line:column`:
- Return cached result immediately
- Update cache asynchronously
- Invalidate on file save

### Timeout Handling

```typescript
const LEAN_TIMEOUT_MS = 5000;

async function withTimeout<T>(promise: Promise<T>, ms: number): Promise<T> {
  const timeout = new Promise<never>((_, reject) => 
    setTimeout(() => reject(new Error('Lean LSP timeout')), ms)
  );
  return Promise.race([promise, timeout]);
}

// Usage
const goals = await withTimeout(leanProxy.getGoals(file, line, col), LEAN_TIMEOUT_MS);
```

---

## Related Specifications

- `61-LEAN-LSP-MCP.md` - MCP tool details
- `62-PROOF-TRACKING.md` - Proof state management
- `63-THEOREM-LIBRARY.md` - Theorem storage and search
- `64-TACTIC-SUGGESTIONS.md` - Suggestion ranking algorithm
- `67-LEAN4-ERROR-HANDLING.md` - Error formatting

---

*"Types are proofs. Proofs are types. The sidepanel shows both."*
