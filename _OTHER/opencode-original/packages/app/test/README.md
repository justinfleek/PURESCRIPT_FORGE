# Test Infrastructure

Practical testing focused on real user workflows and realistic data distributions.

## Test Philosophy

**No busy work** - Tests sample from probable distributions, not exhaustive edge cases.
**Real workflows** - Test what users actually do.
**Performance matters** - Benchmark realistic scenarios.

## Test Types

### 1. Unit Tests
**Location:** `test/utils/**/*.test.ts`

Pure function tests for utilities. Fast, focused.

### 2. Integration Tests  
**Location:** `test/components/integration.test.tsx`

Test complete user workflows, not isolated components.

### 3. Performance Tests
**Location:** `test/performance/realistic.test.ts`

Benchmark typical usage patterns:
- Typical conversation: 10 messages
- Long conversation: 50 messages  
- Empty state: 0 messages

### 4. Optimization Tests
**Location:** `test/optimization/**/*.test.ts`

Prevent regressions in bundle size and render performance.

## Running Tests

```bash
bun run test              # All tests
bun run test:unit         # Unit tests only
bun run test:performance  # Performance benchmarks
bun run test:optimization  # Regression tests
```

## What We Test

✅ **Real user workflows** - Complete flows, not isolated clicks
✅ **Realistic data** - Typical message counts, file paths, etc.
✅ **Performance targets** - Based on actual usage patterns
✅ **Critical paths** - What users actually use

## What We Don't Test

❌ Exhaustive property tests on every input
❌ Edge cases that never happen in practice
❌ Theoretical invariants without user value
❌ Busy work for coverage metrics
