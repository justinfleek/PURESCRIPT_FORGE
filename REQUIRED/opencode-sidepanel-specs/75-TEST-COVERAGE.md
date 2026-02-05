# 75-TEST-COVERAGE: Coverage Requirements and Reporting

## Overview

Code coverage requirements ensure adequate test coverage across the codebase. This document defines coverage targets, measurement, and reporting.

---

## Coverage Targets

### Overall Targets

| Metric | Minimum | Target | Excellent |
|--------|---------|--------|-----------|
| Line Coverage | 70% | 80% | 90% |
| Branch Coverage | 60% | 75% | 85% |
| Function Coverage | 75% | 85% | 95% |

### Component-Specific Targets

| Component | Line | Branch | Notes |
|-----------|------|--------|-------|
| Core Logic | 85% | 80% | Balance, sessions, state |
| UI Components | 70% | 65% | Halogen components |
| Bridge Server | 80% | 75% | API, WebSocket |
| Utilities | 90% | 85% | Pure functions |
| FFI Bindings | 60% | 50% | Integration heavy |

---

## Critical Paths (100% Required)

These paths must have complete test coverage:

1. **Balance Tracking**
   - Diem extraction from headers
   - Balance state updates
   - Alert threshold logic

2. **Session Management**
   - Create/delete sessions
   - Message persistence
   - Branch operations

3. **State Recovery**
   - Crash recovery
   - Snapshot restore
   - Import/export

4. **Security**
   - API key handling
   - Input validation
   - XSS prevention

---

## Coverage Configuration

### Jest (TypeScript)

```javascript
// jest.config.js
module.exports = {
  collectCoverage: true,
  collectCoverageFrom: [
    'src/**/*.{ts,tsx}',
    '!src/**/*.d.ts',
    '!src/**/*.test.ts',
    '!src/types/**'
  ],
  coverageThreshold: {
    global: {
      branches: 60,
      functions: 75,
      lines: 70,
      statements: 70
    },
    // Critical paths
    'src/balance/**': {
      branches: 80,
      functions: 90,
      lines: 85
    },
    'src/session/**': {
      branches: 80,
      functions: 90,
      lines: 85
    }
  },
  coverageReporters: ['text', 'lcov', 'html', 'json-summary']
};
```

### PureScript

```purescript
-- spago test with coverage
-- Use purescript-coverage or instrument with tarpaulin

-- In CI:
-- spago test --coverage
```

---

## Coverage Reports

### Terminal Output

```
-----------------------------|---------|----------|---------|---------|
File                         | % Stmts | % Branch | % Funcs | % Lines |
-----------------------------|---------|----------|---------|---------|
All files                    |   82.5  |   75.3   |   86.2  |   81.8  |
 src/balance                 |   95.2  |   88.5   |   98.0  |   94.8  |
  tracker.ts                 |   96.4  |   90.0   |  100.0  |   95.8  |
  alerts.ts                  |   93.2  |   85.7   |   95.0  |   93.1  |
 src/session                 |   88.4  |   82.1   |   92.3  |   87.6  |
  manager.ts                 |   90.2  |   85.0   |   95.0  |   89.5  |
  branching.ts               |   85.3  |   78.6   |   88.9  |   84.2  |
 src/websocket               |   78.6  |   71.4   |   82.4  |   77.9  |
  protocol.ts                |   82.1  |   75.0   |   86.7  |   81.3  |
  reconnect.ts               |   73.5  |   66.7   |   76.9  |   72.8  |
-----------------------------|---------|----------|---------|---------|
```

### HTML Report Structure

```
coverage/
├── lcov-report/
│   ├── index.html          # Overview
│   ├── src/
│   │   ├── balance/
│   │   │   ├── tracker.ts.html
│   │   │   └── alerts.ts.html
│   │   ├── session/
│   │   │   ├── manager.ts.html
│   │   │   └── branching.ts.html
│   │   └── ...
│   └── ...
├── lcov.info               # LCOV format for CI
└── coverage-summary.json   # Machine-readable
```

---

## CI Integration

### GitHub Actions

```yaml
# .github/workflows/test.yml
- name: Run tests with coverage
  run: pnpm test:coverage

- name: Check coverage thresholds
  run: |
    COVERAGE=$(cat coverage/coverage-summary.json | jq '.total.lines.pct')
    if (( $(echo "$COVERAGE < 70" | bc -l) )); then
      echo "Coverage below threshold: $COVERAGE%"
      exit 1
    fi

- name: Upload coverage to Codecov
  uses: codecov/codecov-action@v3
  with:
    files: ./coverage/lcov.info
    fail_ci_if_error: true

- name: Comment coverage on PR
  uses: romeovs/lcov-reporter-action@v0.3.1
  with:
    lcov-file: ./coverage/lcov.info
    github-token: ${{ secrets.GITHUB_TOKEN }}
```

### Coverage Badge

```markdown
[![codecov](https://codecov.io/gh/weyl-ai/opencode-sidepanel/branch/main/graph/badge.svg)](https://codecov.io/gh/weyl-ai/opencode-sidepanel)
```

---

## Measuring Coverage

### Running Coverage

```bash
# Full coverage report
pnpm test:coverage

# Coverage for specific path
pnpm test:coverage -- --collectCoverageFrom="src/balance/**"

# Watch mode with coverage
pnpm test:coverage -- --watch

# Generate HTML report
pnpm test:coverage -- --coverageReporters=html
open coverage/lcov-report/index.html
```

### Viewing Uncovered Lines

```bash
# Show uncovered lines in terminal
pnpm test:coverage -- --verbose

# Generate detailed report
pnpm test:coverage -- --coverageReporters=text-lcov | less
```

---

## Coverage Exclusions

### Legitimate Exclusions

```typescript
/* istanbul ignore next */
function debugOnly(): void {
  // Debug code not worth testing
}

/* istanbul ignore if */
if (process.env.NODE_ENV === 'development') {
  // Dev-only code
}
```

### Patterns to Exclude

```javascript
// jest.config.js
coveragePathIgnorePatterns: [
  '/node_modules/',
  '/__tests__/',
  '/__mocks__/',
  '/test/',
  '\\.d\\.ts$',
  '\\.stories\\.',
  '/generated/'
]
```

---

## Coverage Quality

### Good Coverage vs. Bad Coverage

```typescript
// BAD: High coverage, low value
test('getBalance returns balance', () => {
  expect(getBalance()).toBeDefined();  // Covers line, tests nothing
});

// GOOD: Meaningful coverage
test('getBalance extracts diem from headers', () => {
  const headers = new Headers({ 'x-venice-balance-diem': '42.5' });
  const balance = extractBalance(headers);
  expect(balance.diem).toBe(42.5);
});

test('getBalance handles missing header', () => {
  const headers = new Headers({});
  const balance = extractBalance(headers);
  expect(balance.diem).toBe(0);
});
```

### Branch Coverage Importance

```typescript
// Function with 3 branches
function getAlertLevel(diem: number): AlertLevel {
  if (diem < 5) return 'critical';  // Branch 1
  if (diem < 10) return 'warning';  // Branch 2
  return 'normal';                   // Branch 3
}

// Tests should cover all branches
test('critical when diem < 5', () => {
  expect(getAlertLevel(3)).toBe('critical');
});

test('warning when diem < 10', () => {
  expect(getAlertLevel(7)).toBe('warning');
});

test('normal when diem >= 10', () => {
  expect(getAlertLevel(15)).toBe('normal');
});
```

---

## Coverage Trends

### Tracking Over Time

```
Week 1:  ████████░░ 72%
Week 2:  █████████░ 75%
Week 3:  █████████░ 78%
Week 4:  ██████████ 81%
```

### Preventing Regression

```yaml
# Block PRs that reduce coverage
- name: Check coverage regression
  run: |
    BASE_COV=$(curl -s "$CODECOV_API/main" | jq '.totals.coverage')
    PR_COV=$(cat coverage/coverage-summary.json | jq '.total.lines.pct')
    if (( $(echo "$PR_COV < $BASE_COV - 1" | bc -l) )); then
      echo "Coverage decreased by more than 1%"
      exit 1
    fi
```

---

## Related Specifications

- `70-TESTING-STRATEGY.md` - Overall strategy
- `81-CI-CD-CONFIGURATION.md` - CI integration
- `71-UNIT-TESTING.md` - Unit tests

---

*"Coverage is a measure of confidence, not quality. Aim for meaningful coverage."*
