# Running Tests for Console App

## ⭐ Quick Start (Recommended)

```bash
# From project root
nix run .#console-app-test
```

This automatically:
- Sets up the environment (purs, spago, nodejs)
- Installs test dependencies
- Runs all tests

## Method 1: Using Nix Develop Shell

Enter the Nix development shell where all tools (spago, purs, nodejs) are available:

```bash
# From project root
nix develop

# Then navigate to console/app
cd packages/console/app

# Run tests
spago -x test.dhall test
```

**Note:** `nix develop` can take 5-15 minutes on first run to evaluate all dependencies.

## Method 2: Using Nix Run (Direct) ⭐ RECOMMENDED

Run tests directly using Nix (configured in flake.nix):

```bash
# From project root
nix run .#console-app-test
```

This is the **fastest and most reliable** method - it sets up everything automatically.

## Method 3: WSL (Windows Subsystem for Linux)

If you're on Windows and have WSL:

```bash
# Enter WSL
wsl

# Navigate to project (Windows paths are mounted at /mnt/c/)
cd /mnt/c/Users/justi/Desktop/CODER

# Run tests directly via flake
nix run .#console-app-test
```

## Test Structure

Tests are organized in:
- `test/unit/` - Unit tests for individual modules
- `test/property/` - Property-based tests
- `test/integration/` - Integration tests

All tests are collected in `test/Main.purs` which serves as the entry point.

## Troubleshooting

### "spago: command not found"

Use the flake app instead:
```bash
nix run .#console-app-test
```

### "test.dhall not found"

The `test.dhall` file should exist in `packages/console/app/`. If missing, it's been created automatically.

### "Module not found" errors

The flake app automatically installs dependencies. If running manually:
```bash
spago -x test.dhall install
```

### Tests fail to compile

Check that all test dependencies are in `test.dhall`:
- `spec` - Test framework
- `spec-discovery` - Auto-discovery (optional)
- `quickcheck` - Property testing
- `quickcheck-laws` - Property test laws

## Finding Bugs

When tests run, they will:
1. **Execute all test cases** - Each `it "description"` block runs
2. **Report failures** - Tests with "BUG:" comments that fail indicate actual bugs
3. **Show passing tests** - Tests that pass confirm correct behavior

**Bugs are discovered when tests FAIL.** The "BUG:" comments document suspected issues, but running tests confirms whether they exist.

## Next Steps After Running Tests

1. **Document failures** - Record which tests fail
2. **Fix bugs** - Address the failing test cases
3. **Re-run tests** - Verify fixes work
4. **Update testing plan** - Mark bugs as fixed in `docs/PRODUCTION_READINESS_TESTING_PLAN.md`
