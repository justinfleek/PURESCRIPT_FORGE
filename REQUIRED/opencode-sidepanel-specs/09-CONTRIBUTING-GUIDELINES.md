# 09-CONTRIBUTING-GUIDELINES: How to Contribute

## Overview

This document outlines how to contribute to the OpenCode Sidepanel project, including code standards, PR process, and community guidelines.

---

## Getting Started

### Prerequisites

1. Read the specification suite (start with `00-SPEC-INDEX.md`)
2. Set up development environment (`05-DEVELOPMENT-SETUP.md`)
3. Understand the architecture (`02-SYSTEM-ARCHITECTURE.md`)

### First-Time Setup

```bash
# Clone repository
git clone https://github.com/your-org/opencode-sidepanel
cd opencode-sidepanel

# Enter Nix environment
nix develop

# Install dependencies
npm install
cd frontend && spago install && cd ..
cd bridge && npm install && cd ..

# Run tests
npm test

# Start development
npm run dev
```

---

## Contribution Types

### 1. Bug Fixes

```
Priority: High
Process: Issue → Branch → Fix → Test → PR
Branch naming: fix/issue-number-short-description
```

### 2. Features

```
Priority: Medium
Process: RFC → Approval → Branch → Implement → Test → PR
Branch naming: feat/feature-name
```

### 3. Documentation

```
Priority: Medium
Process: Branch → Write → Review → PR
Branch naming: docs/topic-name
```

### 4. Performance

```
Priority: Medium
Process: Benchmark → Profile → Optimize → Verify → PR
Branch naming: perf/optimization-name
```

---

## Code Standards

### Critical Rules

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  RULE 1: FULL FILE READS                                                    │
│  NEVER use grep or partial file views. ALWAYS read complete files.          │
├─────────────────────────────────────────────────────────────────────────────┤
│  RULE 2: CODE IS TRUTH                                                      │
│  NEVER delete working code to satisfy TypeScript.                           │
│  ALWAYS update type definitions to match working code.                      │
├─────────────────────────────────────────────────────────────────────────────┤
│  RULE 3: READ BEFORE WRITE                                                  │
│  ALWAYS read related specs before implementing.                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### PureScript Style

```purescript
-- Good: Explicit types, clear naming
calculateBurnRate :: Array BalanceSnapshot -> Number
calculateBurnRate snapshots =
  let
    sorted = sortBy (comparing _.timestamp) snapshots
    deltas = zipWith calcDelta sorted (drop 1 sorted)
  in
    average deltas

-- Bad: Implicit types, unclear naming
calc x = avg $ zipWith f x (drop 1 x)
```

### TypeScript Style

```typescript
// Good: Explicit types, error handling
async function fetchBalance(): Promise<Result<Balance, ApiError>> {
  try {
    const response = await venice.get('/balance');
    return Ok(parseBalance(response));
  } catch (error) {
    return Err(toApiError(error));
  }
}

// Bad: Any types, no error handling
async function fetchBalance() {
  const response = await venice.get('/balance');
  return response;
}
```

---

## Pull Request Process

### Before Submitting

- [ ] Read related specification files
- [ ] Run all tests (`npm test`)
- [ ] Run linter (`npm run lint`)
- [ ] Update documentation if needed
- [ ] Add tests for new features
- [ ] Verify no console errors

### PR Template

```markdown
## Description
Brief description of changes

## Related Specs
- `XX-SPEC-NAME.md` - How this relates

## Type of Change
- [ ] Bug fix
- [ ] New feature
- [ ] Documentation
- [ ] Performance improvement
- [ ] Refactoring

## Testing
- [ ] Unit tests added/updated
- [ ] Integration tests added/updated
- [ ] Manual testing completed

## Screenshots (if UI changes)
Before | After

## Checklist
- [ ] Code follows style guidelines
- [ ] Self-review completed
- [ ] Documentation updated
- [ ] Tests pass locally
```

### Review Process

1. **Automated checks** - CI runs tests, linting, type checking
2. **Code review** - At least 1 approval required
3. **Spec review** - Verify alignment with specifications
4. **Merge** - Squash and merge to main

---

## Commit Messages

### Format

```
type(scope): subject

body (optional)

footer (optional)
```

### Types

| Type | Description |
|------|-------------|
| `feat` | New feature |
| `fix` | Bug fix |
| `docs` | Documentation |
| `style` | Formatting |
| `refactor` | Code restructuring |
| `perf` | Performance |
| `test` | Tests |
| `chore` | Maintenance |

### Examples

```
feat(dashboard): add token usage sparkline

fix(balance): correct UTC midnight calculation
Fixes #123

docs(api): update Venice endpoint documentation

perf(websocket): reduce reconnection delay
```

---

## Testing Requirements

### Coverage Targets

| Component | Target |
|-----------|--------|
| PureScript | 80% |
| TypeScript | 80% |
| Integration | 70% |
| E2E | Critical paths |

### Test Patterns

```purescript
-- Unit test
describe "calculateBurnRate" do
  it "returns 0 for empty array" do
    calculateBurnRate [] `shouldEqual` 0.0
  
  it "calculates correct rate for decreasing balance" do
    let snapshots = [{ diem: 100.0, timestamp: t1 }, { diem: 90.0, timestamp: t2 }]
    calculateBurnRate snapshots `shouldEqual` 10.0
```

---

## Issue Guidelines

### Bug Reports

```markdown
**Environment**
- OS: 
- Browser:
- Version:

**Description**
Clear description of the bug

**Steps to Reproduce**
1. 
2. 
3. 

**Expected Behavior**

**Actual Behavior**

**Screenshots/Logs**
```

### Feature Requests

```markdown
**Problem**
What problem does this solve?

**Proposed Solution**
How should it work?

**Related Specs**
Which specs does this relate to?

**Alternatives Considered**
Other approaches?
```

---

## Community Guidelines

### Be Respectful
- Welcome newcomers
- Provide constructive feedback
- Assume good intent

### Be Collaborative
- Share knowledge
- Help with reviews
- Mentor others

### Be Professional
- Focus on the work
- Keep discussions technical
- Respect time zones

---

## Getting Help

- **Documentation**: Start with `00-SPEC-INDEX.md`
- **Discussions**: GitHub Discussions for questions
- **Issues**: GitHub Issues for bugs/features
- **Chat**: Discord for real-time help

---

*"Good contributions make great software."*
