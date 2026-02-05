# 09-CONTRIBUTION-GUIDELINES: How to Contribute

## Overview

Guidelines for contributing to the OpenCode Sidepanel project. Whether you're fixing bugs, adding features, or improving documentation, this guide will help you get started.

---

## Getting Started

### 1. Fork and Clone

```bash
# Fork on GitHub, then clone
git clone https://github.com/YOUR_USERNAME/opencode-sidepanel.git
cd opencode-sidepanel

# Add upstream remote
git remote add upstream https://github.com/weyl-ai/opencode-sidepanel.git
```

### 2. Set Up Development Environment

```bash
# Enter Nix development shell
nix develop

# Install dependencies
pnpm install

# Start development servers
pnpm dev
```

### 3. Create a Branch

```bash
# Sync with upstream
git fetch upstream
git checkout -b feature/your-feature-name upstream/main
```

---

## Code Standards

### Critical Rules

> **READ THESE BEFORE WRITING ANY CODE**

```
1. FULL FILE READS ONLY
   - Never use grep or partial views
   - Always read complete files
   - Understand full context before changes

2. CODE IS TRUTH, TYPES DESCRIBE
   - Working code is always correct
   - Never delete code to satisfy TypeScript
   - Update type definitions to match code

3. READ SPECS BEFORE IMPLEMENTING
   - Check relevant spec files first
   - Understand the design intent
   - Ask questions if unclear
```

### PureScript Style

```purescript
-- Use explicit imports
import Prelude
import Data.Maybe (Maybe(..))
import Data.Array (filter, map)

-- Type signatures required for top-level
myFunction :: forall m. MonadAff m => String -> m Unit

-- Descriptive names
calculateDiemBurnRate :: Array TokenUsage -> Number
-- Not: calcRate

-- Document complex functions
-- | Calculates the weighted average consumption rate
-- | using exponential decay for older samples
calculateConsumptionRate :: Array Sample -> Number
```

### TypeScript Style

```typescript
// Explicit return types
function calculateBurnRate(samples: TokenSample[]): number {
  // ...
}

// Use interfaces over types for objects
interface Session {
  id: string;
  title: string;
  messages: Message[];
}

// Descriptive error messages
throw new Error(`Session not found: ${sessionId}`);
```

### CSS Style

```css
/* Use CSS variables for theming */
.component {
  background: var(--color-bg-surface);
  color: var(--color-text-primary);
}

/* BEM naming convention */
.session-panel { }
.session-panel__header { }
.session-panel__header--collapsed { }

/* Mobile-first responsive */
.widget {
  width: 100%;
}

@media (min-width: 768px) {
  .widget {
    width: 50%;
  }
}
```

---

## Commit Messages

### Format

```
<type>(<scope>): <subject>

<body>

<footer>
```

### Types

| Type | Description |
|------|-------------|
| `feat` | New feature |
| `fix` | Bug fix |
| `docs` | Documentation |
| `style` | Formatting (no code change) |
| `refactor` | Code restructuring |
| `perf` | Performance improvement |
| `test` | Adding tests |
| `chore` | Maintenance |

### Examples

```
feat(dashboard): add token usage sparkline

Added a mini sparkline chart to the balance widget
showing the last 24 hours of token consumption.

Closes #123
```

```
fix(websocket): handle reconnection race condition

The previous implementation could leave orphan
connections when rapid reconnects occurred.

- Added connection mutex
- Cleaned up stale connections on reconnect
- Added regression test

Fixes #456
```

---

## Pull Request Process

### Before Submitting

- [ ] Code follows style guidelines
- [ ] All tests pass (`pnpm test`)
- [ ] New features have tests
- [ ] Documentation updated if needed
- [ ] Spec files referenced in PR description
- [ ] No console.log or debug code

### PR Template

```markdown
## Description
Brief description of changes

## Related Specs
- `50-DASHBOARD-LAYOUT.md`
- `51-DIEM-TRACKER-WIDGET.md`

## Type of Change
- [ ] Bug fix
- [ ] New feature
- [ ] Breaking change
- [ ] Documentation

## Testing
- [ ] Unit tests added/updated
- [ ] Integration tests added/updated
- [ ] Manual testing completed

## Screenshots (if UI change)
[Add screenshots here]

## Checklist
- [ ] Code follows project style
- [ ] Self-reviewed my code
- [ ] Added comments for complex logic
- [ ] Documentation updated
- [ ] No new warnings
```

### Review Process

1. **Automated checks** - CI must pass
2. **Code review** - At least one approval required
3. **Spec compliance** - Changes match specifications
4. **Testing** - Adequate test coverage

---

## Testing Requirements

### Unit Tests

```purescript
-- Every module needs tests
-- frontend/test/Sidepanel/BalanceSpec.purs

spec :: Spec Unit
spec = describe "Balance calculations" do
  it "calculates burn rate correctly" do
    let samples = [...]
    calculateBurnRate samples `shouldEqual` 5.2
```

### Integration Tests

```typescript
// Bridge API tests
describe('WebSocket Protocol', () => {
  it('handles balance updates', async () => {
    const ws = await connect();
    ws.send({ method: 'balance.get' });
    const response = await ws.receive();
    expect(response.result).toHaveProperty('diem');
  });
});
```

### E2E Tests

```typescript
// Playwright tests for critical flows
test('dashboard shows balance', async ({ page }) => {
  await page.goto('/');
  await expect(page.locator('.diem-tracker')).toBeVisible();
  await expect(page.locator('.balance-value')).toContainText('Diem');
});
```

---

## Documentation

### When to Update Docs

- New features → Update relevant spec file
- API changes → Update protocol docs
- Bug fixes → Add to known issues if relevant
- Breaking changes → Update migration guide

### Spec File Updates

```markdown
## Changelog

### v1.1.0
- Added sparkline to balance widget
- Fixed timezone handling in countdown

### v1.0.0
- Initial specification
```

---

## Issue Reporting

### Bug Reports

```markdown
**Describe the bug**
Clear description of what happened

**To Reproduce**
1. Go to '...'
2. Click on '...'
3. See error

**Expected behavior**
What should have happened

**Screenshots**
If applicable

**Environment**
- OS: [e.g., macOS 14.0]
- Browser: [e.g., Chrome 120]
- Node version: [e.g., 20.10.0]

**Additional context**
Any other relevant information
```

### Feature Requests

```markdown
**Is this related to a problem?**
Description of the problem

**Describe the solution**
What you'd like to happen

**Alternatives considered**
Other solutions you've thought about

**Related specs**
Which spec files this relates to
```

---

## Community

### Communication

- **GitHub Issues** - Bug reports, feature requests
- **GitHub Discussions** - Questions, ideas
- **Pull Requests** - Code contributions

### Code of Conduct

- Be respectful and inclusive
- Focus on constructive feedback
- Help others learn and grow
- Assume good intentions

---

## License

By contributing, you agree that your contributions will be licensed under the project's MIT License.

---

*"Good contributions make great software. Thank you for helping."*
