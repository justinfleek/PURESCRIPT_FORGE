# Test Infrastructure Implementation Plan

**Date**: 2026-02-05  
**Status**: IN PROGRESS  
**Goal**: Comprehensive test suite covering all requirements

---

## Overview

This document tracks the implementation of comprehensive testing infrastructure across all languages and components.

---

## Part 1: Test Framework Setup

### PureScript Test Infrastructure

**Status**: ⚠️ Partial (spec + quickcheck exist in some packages)

**Required Actions:**
- [ ] Add `spec` and `quickcheck` to all PureScript package dependencies
- [ ] Create test directory structure: `test/unit/`, `test/property/`, `test/integration/`
- [ ] Set up test runners for each package
- [ ] Configure CI/CD to run PureScript tests

**Packages Needing Setup:**
- `packages/console/app`
- `packages/console/core`
- `packages/app`
- `packages/ui`
- `packages/util`
- `src/bridge-server-ps`
- `src/sidepanel-ps`
- `src/render-api-ps`

### Haskell Test Infrastructure

**Status**: ❌ Missing

**Required Actions:**
- [ ] Add `hspec` and `QuickCheck` to all `.cabal` files
- [ ] Create test suites in each package
- [ ] Set up test directories: `test/unit/`, `test/property/`, `test/integration/`
- [ ] Configure CI/CD to run Haskell tests

**Packages Needing Setup:**
- `src/render-gateway-hs`
- `src/render-cas-hs`
- `src/render-compliance-hs`
- `src/render-billing-hs`
- `src/render-clickhouse-hs`
- `src/bridge-database-hs`
- `src/bridge-analytics-hs`

### Lean4 Proof Verification

**Status**: ✅ Active (but proofs incomplete)

**Required Actions:**
- [ ] Complete all proofs (remove admit/sorry)
- [ ] Set up CI/CD to verify proofs (`lake build`)
- [ ] Document runtime invariants where proofs aren't feasible

---

## Part 2: Test Type Implementation

### Unit Tests

**Target Coverage**: 80%+ for PureScript/Haskell, 70%+ for Python

**Priority Components:**
1. State reducers (100% coverage required)
2. Formatters (100% coverage required)
3. Pure functions (100% coverage required)
4. API clients (90% coverage required)
5. Components (70% coverage required)

### Property Tests

**Realistic Distributions Required:**
- Balance: Normal(μ=50, σ=20), bounded [0, 100]
- Timestamps: Uniform across UTC day
- Session durations: Exponential(λ=0.1)
- History length: Uniform [1, maxHistory]
- Undo/redo actions: Markov chain (40% undo, 10% redo, 50% new state)

**Properties to Test:**
- Balance invariants (non-negativity, consumption priority)
- Undo/redo properties (history invariants, branching)
- State reducer properties (idempotency, determinism)
- Format conversion properties (round-trip, idempotency)
- Countdown timer properties (never negative, UTC correctness)

### Integration Tests

**Required:**
- Gateway ↔ Backend integration
- CAS upload/fetch integration
- WebSocket bridge integration
- Database layer integration
- Job management integration

### E2E Tests

**Required:**
- Render API E2E (video/image generation)
- Sidepanel UI E2E
- Console package E2E
- Browser E2E (Playwright)

### Regression Tests

**Required:**
- Known bug tests
- Historical failure tests
- Breaking change tests

### Undo/Redo Tests

**Status**: ⚠️ Partial (property tests exist, but need comprehensive suite)

**Required:**
- History state tests
- Branching tests
- State restoration tests
- Edge case tests (empty history, max history, etc.)

### State Persistence Tests

**Required:**
- Save state tests
- Load state tests
- State migration tests
- State corruption recovery tests

### Performance Tests

**Required:**
- Latency tests (p50, p95, p99)
- Throughput tests
- Gateway performance tests
- CAS performance tests

**Targets:**
- State update latency: <50ms p99
- UI response time: <100ms
- Initial load time: <1s

### Memory Tests

**Required:**
- Memory leak detection
- Memory usage benchmarks
- Cache memory footprint tests

### Browser Tests

**Required:**
- Browser compatibility tests (Chrome, Firefox, Safari)
- Cross-browser tests
- Mobile browser tests
- Browser performance tests

### Caching Tests

**Required:**
- Cache hit/miss tests
- Cache invalidation tests
- Cache performance tests

### Optimization Tests

**Required:**
- Bundle size tests
- Optimization regression tests
- Performance optimization tests

---

## Part 3: Implementation Priority

### Phase 1: Foundation (Week 1)
1. Set up test frameworks for all languages
2. Create test directory structures
3. Configure CI/CD pipelines
4. Set up coverage reporting

### Phase 2: Unit Tests (Week 2)
1. State reducers (100% coverage)
2. Formatters (100% coverage)
3. Pure functions (100% coverage)
4. API clients (90% coverage)

### Phase 3: Property Tests (Week 3)
1. Balance properties
2. Undo/redo properties
3. State reducer properties
4. Format conversion properties

### Phase 4: Integration Tests (Week 4)
1. Gateway ↔ Backend
2. CAS operations
3. WebSocket bridge
4. Database layer

### Phase 5: E2E & Specialized Tests (Week 5)
1. E2E tests
2. Regression tests
3. Performance tests
4. Memory tests
5. Browser tests

---

## Part 4: Test Infrastructure Files

### PureScript Test Setup

**File**: `packages/console/app/spago.dhall` (or `spago.yaml`)

```dhall
test:
  dependencies:
    - spec
    - spec-discovery
    - quickcheck
    - quickcheck-laws
```

**File**: `packages/console/app/test/Main.purs`

```purescript
module Test.Main where

import Prelude
import Effect (Effect)
import Test.Spec (describe, it)
import Test.Spec.Runner (runSpec)
import Test.Spec.Reporter.Console (consoleReporter)

main :: Effect Unit
main = runSpec [consoleReporter] do
  describe "Console App Tests" do
    -- Unit tests
    -- Property tests
    -- Integration tests
```

### Haskell Test Setup

**File**: `src/render-gateway-hs/render-gateway-hs.cabal`

```cabal
test-suite render-gateway-tests
  type: exitcode-stdio-1.0
  main-is: Test.hs
  hs-source-dirs: test
  build-depends:
    base >= 4.18 && < 5.0
    , render-gateway-hs
    , hspec >= 2.10
    , QuickCheck >= 2.14
    , hspec-discover >= 2.10
  default-language: Haskell2010
  ghc-options: -Wall -O2
```

**File**: `src/render-gateway-hs/test/Test.hs`

```haskell
import Test.Hspec
import Test.QuickCheck

main :: IO ()
main = hspec $ do
  describe "Render Gateway" $ do
    -- Unit tests
    -- Property tests
    -- Integration tests
```

---

## Part 5: CI/CD Integration

### GitHub Actions Workflow

**File**: `.github/workflows/tests.yml`

```yaml
name: Tests

on: [push, pull_request]

jobs:
  purescript-tests:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: purescript-contrib/setup-purescript@main
      - run: spago test
      
  haskell-tests:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: haskell/actions/setup@v2
      - run: cabal test
      
  lean4-proofs:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: leanprover/lean4-action@v1
      - run: lake build
```

---

## Part 6: Coverage Reporting

### Coverage Targets

- PureScript: 80%+
- Haskell: 80%+
- Python: 70%+
- Lean4: 100% (all proofs complete)

### Coverage Tools

- PureScript: `purescript-coverage` (if available) or manual tracking
- Haskell: `hpc` (Haskell Program Coverage)
- Python: `pytest-cov`
- Lean4: Proof verification (no coverage needed)

---

## Part 7: Progress Tracking

### Current Status

- [ ] PureScript test infrastructure: ⚠️ Partial
- [ ] Haskell test infrastructure: ❌ Missing
- [ ] Unit tests: ⚠️ Partial
- [ ] Property tests: ⚠️ Partial
- [ ] Integration tests: ⚠️ Partial
- [ ] E2E tests: ⚠️ Partial
- [ ] Regression tests: ❌ Missing
- [ ] Undo/redo tests: ⚠️ Partial
- [ ] State persistence tests: ❌ Missing
- [ ] Performance tests: ⚠️ Partial
- [ ] Memory tests: ⚠️ Partial
- [ ] Browser tests: ❌ Missing
- [ ] Caching tests: ❌ Missing
- [ ] Optimization tests: ❌ Missing

---

**Next Steps:**
1. Set up test frameworks for all languages
2. Create initial test suites
3. Integrate with CI/CD
4. Achieve coverage targets
5. Add specialized test types
