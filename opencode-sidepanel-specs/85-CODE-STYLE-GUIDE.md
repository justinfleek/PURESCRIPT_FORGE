# 85-CODE-STYLE-GUIDE: Formatting and Naming Conventions

## Overview

Consistent code style reduces cognitive load and prevents bikeshedding. This guide covers all languages used in the project: PureScript, TypeScript, CSS, and Lean4.

**Principle:** Readability over cleverness. When in doubt, be explicit.

---

## PureScript Style

### File Structure

```purescript
module Sidepanel.Components.Example where

-- 1. Imports (grouped and sorted)
import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)

import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP

import Sidepanel.State.AppState (AppState)
import Sidepanel.Utils.Time (formatDuration)

-- 2. Type definitions
type Input = { value :: Int }

type State = 
  { count :: Int
  , loading :: Boolean
  }

data Action
  = Initialize
  | Increment
  | Decrement

-- 3. Component definition
component :: forall q m. MonadAff m => H.Component q Input Unit m
component = H.mkComponent { ... }

-- 4. Internal functions (private)
calculateSomething :: Int -> Int
calculateSomething n = n * 2
```

### Import Organization

```purescript
-- Group 1: Prelude (always first, alone)
import Prelude

-- Group 2: Standard library (Data.*, Effect.*, Control.*)
import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.String as String
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff, liftAff)

-- Group 3: External libraries (Halogen, Affjax, etc.)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP

-- Group 4: Project modules
import Sidepanel.Api.WebSocket (ServerMessage)
import Sidepanel.State.Balance (BalanceState)
import Sidepanel.Utils.Format (formatCurrency)
```

### Naming Conventions

| Entity | Convention | Example |
|--------|------------|---------|
| Module | PascalCase, hierarchical | `Sidepanel.Components.Balance` |
| Type | PascalCase | `BalanceState`, `DiemMetrics` |
| Type alias | PascalCase | `type State = { ... }` |
| Data constructor | PascalCase | `Just`, `Nothing`, `Increment` |
| Function | camelCase | `calculateRate`, `formatDiem` |
| Variable | camelCase | `currentBalance`, `isLoading` |
| Constant | camelCase | `maxRetries`, `defaultTimeout` |
| Record field | camelCase | `{ userName :: String }` |
| Type variable | lowercase, single letter or descriptive | `a`, `m`, `state` |

### Type Signatures

```purescript
-- Always provide explicit type signatures for top-level functions
formatBalance :: Number -> String
formatBalance n = ...

-- Multi-line signatures for complex types
component 
  :: forall query input output m
   . MonadAff m
  => H.Component query input output m

-- Align constraints
renderItem
  :: forall m
   . MonadAff m
  => MonadState AppState m
  => Item
  -> H.ComponentHTML Action Slots m
```

### Pattern Matching

```purescript
-- Prefer case expressions for clarity
handleAction = case _ of
  Initialize -> do
    ...
  Increment -> do
    ...
  Decrement -> do
    ...

-- Use guards when appropriate
describe level = case level of
  _ | level < 10 -> "low"
  _ | level < 50 -> "medium"
  _ -> "high"

-- Destructure in function arguments when simple
process (Just x) = x * 2
process Nothing = 0
```

### Record Syntax

```purescript
-- Prefer record update syntax
state { count = state.count + 1 }

-- Use wildcard for multiple updates
state { count = newCount, loading = false, error = Nothing }

-- Long records: one field per line
initialState =
  { count: 0
  , loading: false
  , error: Nothing
  , items: []
  , selectedIndex: 0
  }
```

### Line Length

- Maximum 100 characters
- Break at natural points (after `->`, `=`, operators)
- Indent continuation by 2 spaces

```purescript
-- Good: break after arrow
calculateProjection
  :: BalanceState
  -> Duration
  -> Number
calculateProjection balance duration =
  balance.diem - (balance.metrics.consumptionRate * toHours duration)

-- Good: break long function applications
result = 
  Array.filter isValid
    $ Array.sortBy compareByDate
    $ Array.map transform
    $ items
```

---

## TypeScript Style

### File Structure

```typescript
// 1. Imports (external, then internal)
import { WebSocketServer } from 'ws';
import { z } from 'zod';

import { extractBalance } from './venice/balance';
import { SessionStore } from './session-store';
import type { Session, Message } from './types';

// 2. Constants
const MAX_CONNECTIONS = 100;
const HEARTBEAT_INTERVAL = 30_000;

// 3. Types
interface BridgeConfig {
  port: number;
  veniceApiKey: string;
}

// 4. Main code
export class BridgeServer {
  // ...
}

// 5. Helper functions (private)
function validateConfig(config: unknown): BridgeConfig {
  // ...
}
```

### Naming Conventions

| Entity | Convention | Example |
|--------|------------|---------|
| File | kebab-case | `bridge-server.ts` |
| Class | PascalCase | `BridgeServer` |
| Interface | PascalCase | `BridgeConfig` |
| Type alias | PascalCase | `type SessionId = string` |
| Function | camelCase | `extractBalance` |
| Variable | camelCase | `currentSession` |
| Constant | SCREAMING_SNAKE or camelCase | `MAX_RETRIES` or `maxRetries` |
| Enum value | PascalCase | `AlertLevel.Critical` |
| Generic | Single uppercase | `T`, `K`, `V` |

### Type Annotations

```typescript
// Prefer explicit return types
function calculateRate(history: Snapshot[]): number {
  // ...
}

// Use type inference for obvious cases
const count = 0;  // number is obvious

// Explicit for complex/public APIs
export function createClient(config: ClientConfig): VeniceClient {
  // ...
}

// Prefer interfaces for objects
interface User {
  id: string;
  name: string;
}

// Prefer type for unions/intersections
type Result<T> = { ok: true; value: T } | { ok: false; error: Error };
```

### Async/Await

```typescript
// Always use async/await over .then()
async function fetchBalance(): Promise<Balance> {
  const response = await fetch(url);
  if (!response.ok) {
    throw new Error(`HTTP ${response.status}`);
  }
  return response.json();
}

// Handle errors with try/catch
async function safeFetch(): Promise<Balance | null> {
  try {
    return await fetchBalance();
  } catch (error) {
    console.error('Failed to fetch balance:', error);
    return null;
  }
}
```

### Error Handling

```typescript
// Use custom error classes
class VeniceApiError extends Error {
  constructor(
    public status: number,
    public code: string,
    message: string
  ) {
    super(message);
    this.name = 'VeniceApiError';
  }
}

// Validate with Zod
const BalanceSchema = z.object({
  diem: z.number().nonnegative(),
  usd: z.number().nonnegative(),
});

function parseBalance(data: unknown): Balance {
  return BalanceSchema.parse(data);
}
```

---

## CSS Style

### File Organization

```css
/* 1. CSS Variables (in :root) */
:root {
  --color-primary: #3b82f6;
  --spacing-sm: 8px;
}

/* 2. Reset/base styles */
* {
  box-sizing: border-box;
}

/* 3. Layout components */
.dashboard { }
.sidebar { }

/* 4. UI components (alphabetical) */
.button { }
.card { }
.modal { }

/* 5. Utilities (last) */
.hidden { display: none; }
.sr-only { /* screen reader only */ }
```

### Naming Convention (BEM-inspired)

```css
/* Block */
.diem-tracker { }

/* Element (double underscore) */
.diem-tracker__header { }
.diem-tracker__balance { }
.diem-tracker__countdown { }

/* Modifier (double dash) */
.diem-tracker--warning { }
.diem-tracker--critical { }
.diem-tracker__balance--large { }
```

### CSS Variables

```css
/* Use semantic names */
:root {
  /* Colors */
  --color-primary: #3b82f6;
  --color-warning: #f59e0b;
  --color-error: #ef4444;
  
  /* Text */
  --text-primary: #e4e4e7;
  --text-secondary: #a1a1aa;
  
  /* Surfaces */
  --surface-default: #1a1a1a;
  --surface-elevated: #242424;
  
  /* Spacing */
  --spacing-xs: 4px;
  --spacing-sm: 8px;
  --spacing-md: 16px;
  --spacing-lg: 24px;
  
  /* Typography */
  --font-mono: 'JetBrains Mono', monospace;
  --font-size-sm: 12px;
  --font-size-md: 14px;
  --font-size-lg: 18px;
}
```

### Property Order

```css
.component {
  /* 1. Positioning */
  position: relative;
  top: 0;
  z-index: 10;
  
  /* 2. Display & Box Model */
  display: flex;
  flex-direction: column;
  width: 100%;
  padding: var(--spacing-md);
  margin: 0;
  
  /* 3. Typography */
  font-family: var(--font-mono);
  font-size: var(--font-size-md);
  color: var(--text-primary);
  
  /* 4. Visual */
  background: var(--surface-default);
  border: 1px solid var(--border-subtle);
  border-radius: 8px;
  
  /* 5. Animation */
  transition: background 0.15s ease;
  
  /* 6. Misc */
  cursor: pointer;
}
```

---

## Lean4 Style

### File Structure

```lean
/-
  Module: Sidepanel.Theorems.Balance
  Description: Proofs about balance invariants
  Author: Team
-/

import Mathlib.Data.Nat.Basic
import Sidepanel.Types.Balance

namespace Sidepanel.Theorems.Balance

-- Section: Basic Properties
section BasicProperties

variable (b : Balance)

theorem balance_effective_sum :
    b.effective = b.diem + b.usd := by
  rfl

end BasicProperties

-- Section: Monotonicity
section Monotonicity

theorem consumption_decreases_balance (usage : Usage) (h : usage > 0) :
    (b.consume usage).diem < b.diem := by
  sorry

end Monotonicity

end Sidepanel.Theorems.Balance
```

### Naming Conventions

| Entity | Convention | Example |
|--------|------------|---------|
| File | PascalCase | `Balance.lean` |
| Namespace | PascalCase.Dot.Separated | `Sidepanel.Types` |
| Type/Structure | PascalCase | `BalanceState` |
| Theorem | snake_case | `balance_non_negative` |
| Definition | camelCase | `calculateRate` |
| Variable | camelCase or single letter | `balance`, `b`, `n` |
| Hypothesis | lowercase descriptive | `h`, `hPos`, `hLt` |

### Proof Style

```lean
-- Prefer tactic proofs for complex theorems
theorem complex_result : P := by
  intro x
  cases x with
  | zero => simp
  | succ n => 
    induction n with
    | zero => rfl
    | succ m ih => simp [ih]

-- Use term proofs for simple cases
theorem simple_result : 1 + 1 = 2 := rfl

-- Document non-obvious steps
theorem tricky_result : P := by
  -- First, establish the key lemma
  have key : Q := by exact ...
  -- Now use it to finish
  exact key.trans ...
```

---

## General Principles

### Comments

```purescript
-- Single line comment for quick notes

{- 
  Multi-line comment for longer explanations.
  Use when describing complex logic.
-}

-- | Haddock-style documentation
-- | Describe what the function does, not how
formatBalance :: Number -> String
```

```typescript
// Single line for quick notes

/**
 * JSDoc for public APIs
 * @param balance - The current balance state
 * @returns Formatted string
 */
function formatBalance(balance: number): string { }

// TODO: Description of what needs doing
// FIXME: Description of what's broken
// HACK: Explanation of why this is hacky
```

### Magic Numbers

```typescript
// Bad
if (balance < 5) { ... }

// Good
const BALANCE_WARNING_THRESHOLD = 5;
if (balance < BALANCE_WARNING_THRESHOLD) { ... }

// Exception: truly obvious numbers
const doubled = value * 2;
const percentage = value / 100;
```

### Error Messages

```typescript
// Bad
throw new Error('Failed');

// Good
throw new Error(`Venice API error: ${response.status} ${response.statusText}`);

// Better
throw new VeniceApiError(
  response.status,
  'request_failed',
  `Request to ${endpoint} failed with status ${response.status}`
);
```

---

## Formatting Tools

### PureScript
```bash
# Format with purs-tidy
purs-tidy format-in-place src/**/*.purs

# In justfile
fmt-ps:
  purs-tidy format-in-place src/**/*.purs
```

### TypeScript
```bash
# Format with Prettier
prettier --write "src/**/*.ts"

# Lint with ESLint
eslint src --ext .ts --fix
```

### CSS
```bash
# Format with Prettier
prettier --write "src/**/*.css"

# Lint with Stylelint
stylelint "src/**/*.css" --fix
```

### Lean4
```bash
# No standard formatter yet
# Follow Mathlib style guidelines
```

---

## Pre-commit Checks

```yaml
# .pre-commit-config.yaml
repos:
  - repo: local
    hooks:
      - id: purs-tidy
        name: PureScript Format
        entry: purs-tidy format-in-place
        files: '\.purs$'
      
      - id: prettier
        name: Prettier
        entry: prettier --write
        files: '\.(ts|css|json|md)$'
      
      - id: eslint
        name: ESLint
        entry: eslint --fix
        files: '\.ts$'
```

---

*"Code is read far more often than it is written. Optimize for readability."*
