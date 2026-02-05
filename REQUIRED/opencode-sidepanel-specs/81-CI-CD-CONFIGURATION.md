# 81-CI-CD-CONFIGURATION: GitHub Actions Pipelines

## Overview

This document defines the CI/CD pipelines for the OpenCode Sidepanel project, covering automated testing, building, and deployment.

---

## Pipeline Overview

```
┌─────────────────────────────────────────────────────────────────────────┐
│                          CI/CD PIPELINE                                  │
│                                                                          │
│  Push/PR to main                                                         │
│       │                                                                  │
│       ▼                                                                  │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                       VALIDATION                                 │    │
│  │  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐            │    │
│  │  │ Format  │  │  Lint   │  │  Types  │  │ Audit   │            │    │
│  │  │  Check  │  │         │  │  Check  │  │         │            │    │
│  │  └─────────┘  └─────────┘  └─────────┘  └─────────┘            │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│       │                                                                  │
│       ▼                                                                  │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                         TESTING                                  │    │
│  │  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐            │    │
│  │  │  Unit   │  │Property │  │  Integ  │  │   E2E   │            │    │
│  │  │  Tests  │  │  Tests  │  │  Tests  │  │  Tests  │            │    │
│  │  └─────────┘  └─────────┘  └─────────┘  └─────────┘            │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│       │                                                                  │
│       ▼                                                                  │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                          BUILD                                   │    │
│  │  ┌─────────────────────────────────────────────────────────┐    │    │
│  │  │  Nix Build (all packages)                               │    │    │
│  │  └─────────────────────────────────────────────────────────┘    │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│       │                                                                  │
│       ▼ (main branch only)                                               │
│  ┌─────────────────────────────────────────────────────────────────┐    │
│  │                         DEPLOY                                   │    │
│  │  ┌─────────────────────────────────────────────────────────┐    │    │
│  │  │  Push to Cachix  │  Create Release  │  Notify           │    │    │
│  │  └─────────────────────────────────────────────────────────┘    │    │
│  └─────────────────────────────────────────────────────────────────┘    │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## GitHub Actions Workflows

### Main CI Workflow

```yaml
# .github/workflows/ci.yml
name: CI

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

concurrency:
  group: ${{ github.workflow }}-${{ github.ref }}
  cancel-in-progress: true

jobs:
  # ─────────────────────────────────────────────────────────────────────
  # VALIDATION JOBS
  # ─────────────────────────────────────────────────────────────────────
  
  format:
    name: Format Check
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - uses: DeterminateSystems/nix-installer-action@main
      - uses: DeterminateSystems/magic-nix-cache-action@main
      
      - name: Check PureScript formatting
        run: nix develop --command purs-tidy check frontend/src
      
      - name: Check TypeScript formatting
        run: nix develop --command npx prettier --check "bridge/src/**/*.ts"

  lint:
    name: Lint
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - uses: DeterminateSystems/nix-installer-action@main
      - uses: DeterminateSystems/magic-nix-cache-action@main
      
      - name: Lint TypeScript
        run: nix develop --command npx eslint bridge/src --max-warnings 0

  typecheck:
    name: Type Check
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - uses: DeterminateSystems/nix-installer-action@main
      - uses: DeterminateSystems/magic-nix-cache-action@main
      
      - name: Check PureScript types
        run: nix develop --command bash -c "cd frontend && spago build"
      
      - name: Check TypeScript types
        run: nix develop --command bash -c "cd bridge && npx tsc --noEmit"

  audit:
    name: Security Audit
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - uses: DeterminateSystems/nix-installer-action@main
      - uses: DeterminateSystems/magic-nix-cache-action@main
      
      - name: Audit npm dependencies
        run: nix develop --command bash -c "cd bridge && pnpm audit --audit-level high"

  # ─────────────────────────────────────────────────────────────────────
  # TEST JOBS
  # ─────────────────────────────────────────────────────────────────────
  
  test-unit:
    name: Unit Tests
    runs-on: ubuntu-latest
    needs: [typecheck]
    steps:
      - uses: actions/checkout@v4
      
      - uses: DeterminateSystems/nix-installer-action@main
      - uses: DeterminateSystems/magic-nix-cache-action@main
      
      - name: Run PureScript tests
        run: nix develop --command bash -c "cd frontend && spago test"
      
      - name: Run TypeScript tests
        run: nix develop --command bash -c "cd bridge && pnpm test:unit"
      
      - name: Upload coverage
        uses: codecov/codecov-action@v3
        with:
          files: ./bridge/coverage/lcov.info,./frontend/coverage/lcov.info

  test-property:
    name: Property Tests
    runs-on: ubuntu-latest
    needs: [typecheck]
    steps:
      - uses: actions/checkout@v4
      
      - uses: DeterminateSystems/nix-installer-action@main
      - uses: DeterminateSystems/magic-nix-cache-action@main
      
      - name: Run property tests
        run: nix develop --command bash -c "cd frontend && spago test --main Test.Property.Main"

  test-integration:
    name: Integration Tests
    runs-on: ubuntu-latest
    needs: [test-unit]
    steps:
      - uses: actions/checkout@v4
      
      - uses: DeterminateSystems/nix-installer-action@main
      - uses: DeterminateSystems/magic-nix-cache-action@main
      
      - name: Run integration tests
        run: nix develop --command bash -c "cd bridge && pnpm test:integration"
        env:
          VENICE_API_KEY: ${{ secrets.VENICE_API_KEY_TEST }}

  test-e2e:
    name: E2E Tests
    runs-on: ubuntu-latest
    needs: [test-integration]
    steps:
      - uses: actions/checkout@v4
      
      - uses: DeterminateSystems/nix-installer-action@main
      - uses: DeterminateSystems/magic-nix-cache-action@main
      
      - name: Install Playwright
        run: nix develop --command npx playwright install --with-deps chromium
      
      - name: Run E2E tests
        run: nix develop --command bash -c "cd e2e && pnpm test"
      
      - name: Upload test artifacts
        if: failure()
        uses: actions/upload-artifact@v3
        with:
          name: playwright-report
          path: e2e/playwright-report

  # ─────────────────────────────────────────────────────────────────────
  # BUILD JOB
  # ─────────────────────────────────────────────────────────────────────
  
  build:
    name: Build
    runs-on: ubuntu-latest
    needs: [format, lint, test-unit, test-integration]
    steps:
      - uses: actions/checkout@v4
      
      - uses: DeterminateSystems/nix-installer-action@main
      - uses: DeterminateSystems/magic-nix-cache-action@main
      
      - name: Build all packages
        run: nix build .#all
      
      - name: Upload build artifacts
        uses: actions/upload-artifact@v3
        with:
          name: build
          path: result/

  # ─────────────────────────────────────────────────────────────────────
  # DEPLOY JOB (main branch only)
  # ─────────────────────────────────────────────────────────────────────
  
  deploy:
    name: Deploy
    runs-on: ubuntu-latest
    needs: [build, test-e2e]
    if: github.ref == 'refs/heads/main' && github.event_name == 'push'
    steps:
      - uses: actions/checkout@v4
      
      - uses: DeterminateSystems/nix-installer-action@main
      - uses: DeterminateSystems/magic-nix-cache-action@main
      
      - name: Push to Cachix
        uses: cachix/cachix-action@v12
        with:
          name: weyl-ai
          authToken: ${{ secrets.CACHIX_AUTH_TOKEN }}
          pushFilter: '(-source$|\.tar\.gz$|\.zip$)'
      
      - name: Build and push
        run: |
          nix build .#all
          cachix push weyl-ai result
```

### Release Workflow

```yaml
# .github/workflows/release.yml
name: Release

on:
  push:
    tags:
      - 'v*'

jobs:
  release:
    name: Create Release
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - uses: DeterminateSystems/nix-installer-action@main
      - uses: DeterminateSystems/magic-nix-cache-action@main
      
      - name: Build release
        run: nix build .#release
      
      - name: Create GitHub Release
        uses: softprops/action-gh-release@v1
        with:
          files: |
            result/opencode-sidepanel-*.tar.gz
            result/opencode-sidepanel-*.zip
          generate_release_notes: true
        env:
          GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
```

---

## Nix Flake Checks

```nix
# In flake.nix
{
  checks = forAllSystems (system:
    let pkgs = nixpkgsFor.${system};
    in {
      # Format checks
      format-ps = pkgs.runCommand "format-ps" {} ''
        ${pkgs.purs-tidy}/bin/purs-tidy check ${./frontend/src}
        touch $out
      '';
      
      format-ts = pkgs.runCommand "format-ts" {} ''
        cd ${./.}
        ${pkgs.nodePackages.prettier}/bin/prettier --check "bridge/src/**/*.ts"
        touch $out
      '';
      
      # Type checks
      typecheck-ps = pkgs.runCommand "typecheck-ps" {} ''
        cd ${./frontend}
        ${pkgs.spago}/bin/spago build
        touch $out
      '';
      
      # Unit tests
      test-unit = pkgs.runCommand "test-unit" {} ''
        cd ${./bridge}
        ${pkgs.pnpm}/bin/pnpm test:unit
        touch $out
      '';
      
      # All checks
      all = pkgs.runCommand "all-checks" {
        buildInputs = [
          checks.${system}.format-ps
          checks.${system}.format-ts
          checks.${system}.typecheck-ps
          checks.${system}.test-unit
        ];
      } ''
        touch $out
      '';
    }
  );
}
```

---

## Local Development

### Pre-commit Hooks

```bash
# .husky/pre-commit
#!/bin/sh
. "$(dirname "$0")/_/husky.sh"

# Run format check
just fmt-check || {
  echo "Format check failed. Run 'just fmt' to fix."
  exit 1
}

# Run type check
just typecheck || {
  echo "Type check failed."
  exit 1
}

# Run unit tests
just test-unit || {
  echo "Unit tests failed."
  exit 1
}
```

### justfile CI Commands

```just
# CI commands
ci-format:
  purs-tidy check frontend/src
  npx prettier --check "bridge/src/**/*.ts"

ci-lint:
  npx eslint bridge/src --max-warnings 0

ci-typecheck:
  cd frontend && spago build
  cd bridge && npx tsc --noEmit

ci-test:
  cd frontend && spago test
  cd bridge && pnpm test

ci-all: ci-format ci-lint ci-typecheck ci-test
```

---

## Required Secrets

| Secret | Description | Where Used |
|--------|-------------|------------|
| `VENICE_API_KEY_TEST` | Venice API key for integration tests | test-integration |
| `CACHIX_AUTH_TOKEN` | Cachix authentication | deploy |
| `GITHUB_TOKEN` | GitHub release creation | release |

---

## Branch Protection

Configure for `main` branch:

- [x] Require status checks to pass
  - `format`
  - `lint`
  - `typecheck`
  - `test-unit`
  - `test-integration`
  - `build`
- [x] Require branches to be up to date
- [x] Require pull request reviews (1+)
- [x] Dismiss stale reviews on push
- [x] Require linear history

---

## Related Specifications

- `70-TESTING-STRATEGY.md` - Testing approach
- `04-NIXOS-FLAKE.md` - Nix configuration
- `08-DEVELOPMENT-WORKFLOW.md` - Development process

---

*"CI should be fast, reliable, and informative."*
