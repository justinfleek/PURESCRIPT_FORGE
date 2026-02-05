# 08-DEVELOPMENT-WORKFLOW: Day-to-Day Development Process

## Overview

This document covers the daily workflow for contributing to the OpenCode Sidepanel project, including Git flow, PR process, testing requirements, and code review guidelines.

---

## Daily Workflow

### Starting Work

```bash
# 1. Enter project directory (direnv auto-activates nix shell)
cd opencode-sidepanel

# 2. Pull latest changes
git checkout main
git pull origin main

# 3. Start development servers
just dev

# Output:
# [bridge] Starting on :8765
# [frontend] Watching for changes
# [browser] Opening http://localhost:8765
```

### Making Changes

```bash
# 1. Create feature branch
git checkout -b feature/diem-countdown-animation

# 2. Make changes, tests auto-run on save

# 3. Check formatting
just fmt

# 4. Run full test suite
just test

# 5. Commit with conventional commit message
git add -A
git commit -m "feat(countdown): add pulse animation for critical state"
```

### Ending Work

```bash
# 1. Push branch
git push origin feature/diem-countdown-animation

# 2. Create PR (or use gh cli)
gh pr create --fill

# 3. Stop dev servers (Ctrl+C)
```

---

## Git Branch Strategy

### Branch Types

| Prefix | Purpose | Example |
|--------|---------|---------|
| `main` | Production-ready code | - |
| `feature/` | New features | `feature/proof-panel` |
| `fix/` | Bug fixes | `fix/countdown-drift` |
| `refactor/` | Code refactoring | `refactor/state-management` |
| `docs/` | Documentation | `docs/api-reference` |
| `test/` | Test additions | `test/balance-properties` |

### Branch Naming

```
<type>/<short-description>

Examples:
  feature/diem-countdown
  fix/websocket-reconnect
  refactor/venice-client
  docs/setup-guide
```

Keep names short, lowercase, hyphenated.

---

## Commit Convention

We use [Conventional Commits](https://www.conventionalcommits.org/).

### Format

```
<type>(<scope>): <description>

[optional body]

[optional footer]
```

### Types

| Type | Use For |
|------|---------|
| `feat` | New feature |
| `fix` | Bug fix |
| `docs` | Documentation only |
| `style` | Formatting, no code change |
| `refactor` | Code change that neither fixes nor adds |
| `perf` | Performance improvement |
| `test` | Adding/updating tests |
| `chore` | Build process, auxiliary tools |

### Scopes

| Scope | Area |
|-------|------|
| `bridge` | Bridge server |
| `frontend` | PureScript UI |
| `plugin` | OpenCode plugin |
| `venice` | Venice API integration |
| `websocket` | WebSocket protocol |
| `countdown` | Countdown timer |
| `balance` | Balance tracking |
| `proof` | Lean4 integration |
| `timeline` | Time-travel feature |
| `ci` | CI/CD changes |

### Examples

```bash
# Feature
git commit -m "feat(countdown): implement UTC midnight calculation"

# Bug fix
git commit -m "fix(balance): correct rate calculation for sparse data"

# Breaking change (note the !)
git commit -m "feat(websocket)!: change message format to JSON-RPC 2.0"

# With body
git commit -m "fix(bridge): handle Venice API timeout

The Venice API occasionally times out on large requests.
Added exponential backoff with max 3 retries.

Closes #42"
```

---

## Pull Request Process

### Creating a PR

1. **Push your branch:**
   ```bash
   git push origin feature/my-feature
   ```

2. **Create PR via GitHub or CLI:**
   ```bash
   gh pr create --title "feat(countdown): add pulse animation" --body "..."
   ```

3. **Fill PR template:**
   - Description of changes
   - Related issue (if any)
   - Testing performed
   - Screenshots (for UI changes)

### PR Requirements

Before PR can be merged:

- [ ] All CI checks pass
- [ ] At least 1 approval
- [ ] No unresolved comments
- [ ] Branch is up-to-date with main
- [ ] Commit messages follow convention

### PR Size Guidelines

| Size | Lines Changed | Review Time |
|------|---------------|-------------|
| XS | < 50 | < 15 min |
| S | 50-200 | 15-30 min |
| M | 200-500 | 30-60 min |
| L | 500-1000 | 1-2 hours |
| XL | > 1000 | Split it |

Prefer smaller PRs. If > 500 lines, consider splitting.

---

## Code Review Guidelines

### For Authors

1. **Self-review first** - Read your own diff before requesting review
2. **Explain context** - PR description should explain *why*, not just *what*
3. **Highlight concerns** - Call out areas you're uncertain about
4. **Respond promptly** - Address feedback within 24 hours
5. **Don't take it personally** - Review is about code, not you

### For Reviewers

1. **Be constructive** - Suggest improvements, don't just criticize
2. **Explain reasoning** - Say *why* something should change
3. **Distinguish preferences** - Mark nitpicks as "nit:" or "optional:"
4. **Approve when ready** - Don't block on minor issues
5. **Review promptly** - Within 24 hours if possible

### Review Checklist

- [ ] Code compiles and tests pass
- [ ] Logic is correct and handles edge cases
- [ ] Types are used appropriately
- [ ] Error handling is present
- [ ] No security issues
- [ ] No performance regressions
- [ ] Documentation updated if needed
- [ ] Follows code style guide

---

## Testing Requirements

### Before Committing

```bash
# Run all tests
just test

# Or run specific suites
just test-unit        # Fast, run frequently
just test-integration # Run before PR
just test-e2e         # Run before merge
```

### Test Coverage Requirements

| Area | Minimum Coverage |
|------|-----------------|
| State reducers | 100% |
| Utility functions | 100% |
| API clients | 90% |
| Components | 70% |
| Overall | 80% |

### Writing Tests

Every feature branch should include tests:

```purescript
-- Good: Test accompanies feature
-- frontend/src/Components/Countdown.purs
-- frontend/test/Components/CountdownSpec.purs

-- frontend/test/Components/CountdownSpec.purs
describe "Countdown" do
  it "displays formatted time" do
    let time = { hours: 4, minutes: 23, seconds: 17 }
    formatCountdown time `shouldEqual` "4h 23m 17s"
```

---

## CI/CD Pipeline

### Checks on Every Push

1. **Format Check** - Code is formatted correctly
2. **Type Check** - PureScript and TypeScript compile
3. **Lint** - ESLint passes
4. **Unit Tests** - All unit tests pass
5. **Integration Tests** - API contracts verified

### Checks on PR

All above, plus:
6. **E2E Tests** - Full workflow tests
7. **Coverage Check** - Coverage meets threshold
8. **Build** - Production build succeeds

### Checks on Merge to Main

All above, plus:
9. **Release Build** - Artifacts created
10. **Deploy to Staging** - Automatic deployment

---

## Debugging

### Bridge Server

```bash
# Enable debug logging
SIDEPANEL_DEBUG=1 just bridge-dev

# Or for specific areas
DEBUG=sidepanel:websocket just bridge-dev
DEBUG=sidepanel:venice just bridge-dev
DEBUG=sidepanel:* just bridge-dev
```

### Frontend

```bash
# PureScript build with source maps
spago build --purs-args "--source-maps"

# Browser DevTools
# - React DevTools works with Halogen (somewhat)
# - Network tab for WebSocket messages
# - Console for PureScript debug output
```

### OpenCode Plugin

```bash
# Run OpenCode with plugin debug
OPENCODE_DEBUG=plugins opencode --serve
```

---

## Common Tasks

### Adding a Dependency

**PureScript:**
```bash
cd frontend
spago install package-name
```

**Node.js:**
```bash
cd bridge
pnpm add package-name
```

Update `flake.nix` if adding system dependency.

### Creating a New Component

1. Create component file:
   ```
   frontend/src/Components/MyComponent.purs
   ```

2. Add to parent component's slots

3. Create test file:
   ```
   frontend/test/Components/MyComponentSpec.purs
   ```

4. Create CSS (if needed):
   ```
   frontend/assets/styles/components/my-component.css
   ```

### Updating the Spec

1. Create/edit spec file in `specs/`
2. Update `00-SPEC-INDEX.md` if new file
3. Commit with `docs:` prefix

---

## Troubleshooting Development Issues

### "Build failed" after pull

```bash
# Clean and rebuild
just clean
nix develop
just build
```

### PureScript type errors after merge

```bash
cd frontend
rm -rf .spago output
spago install
spago build
```

### Bridge won't connect to OpenCode

```bash
# Check OpenCode is running with --serve
opencode --serve

# Check port isn't in use
lsof -i :8765

# Check plugin is loaded
opencode config show | grep sidepanel
```

### Tests passing locally but failing in CI

```bash
# Run tests in CI-like environment
nix build .#checks.x86_64-linux.all
```

---

## Release Process

Releases are cut from `main` after Phase completion.

### Version Numbering

```
v0.1.0  - Phase 1 complete
v0.2.0  - Phase 2 complete
v0.3.0  - Phase 3 complete
v1.0.0  - Phase 4 complete (production ready)
```

### Creating a Release

```bash
# 1. Ensure main is clean
git checkout main
git pull

# 2. Run full test suite
just test

# 3. Create tag
git tag -a v0.1.0 -m "Phase 1: Foundation"
git push origin v0.1.0

# 4. GitHub Actions handles the rest
```

---

## Getting Help

- **Stuck on code?** Post in #sidepanel-dev with details
- **Unclear requirements?** Ask in issue comments
- **Review needed?** Request in #code-review
- **CI failing?** Check Actions tab, ask if unclear

---

## Related Specifications

- `05-DEVELOPMENT-SETUP.md` - Initial setup
- `07-PROJECT-STRUCTURE.md` - Directory layout
- `70-TESTING-STRATEGY.md` - Testing in depth
- `85-CODE-STYLE-GUIDE.md` - Code formatting

---

*"Good process enables good work. Bad process prevents it."*
