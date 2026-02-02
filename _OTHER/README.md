# PURESCRIPT_FORGE Workspace

This workspace contains projects following strict development standards for type safety, correctness, and maintainability.

**Rules are implemented as proven code in PureScript/Haskell/Lean4, not just documentation.**

## Projects

- **opencode-dev**: TypeScript/Bun project (migration target)
- **trtllm-serve-main**: Nix/Haskell reference standard
- **opencode-sidepanel-specs**: 99 comprehensive spec files (PureScript/Halogen sidepanel)
- **PRISM**: Color system with Haskell/Lean4 implementations

## Rules Implementation

Rules are implemented in three languages with proofs:

- **PureScript** (`src/rules-ps/`): Application logic
- **Haskell** (`src/rules-hs/`): Performance-critical modules
- **Lean4** (`src/rules-lean/`): Proofs of correctness

### Building Rules

```bash
# Enter dev shell (requires Nix)
nix develop

# Build all rule implementations
nix build .#rules-ps
nix build .#rules-hs
nix build .#rules-lean

# Verify all rules
nix run .#check-rules
```

### Proof Verification

The Lean4 proofs ensure:
- Task completion is verified (`taskCompleteIffAllVerified`)
- Type safety is maintained (`explicitDefaultTypeSafe`, `noTypeEscapes`)
- Banned constructs are unrepresentable

## Spec Integration

### Spec Loader

Loads all 99 specification files completely (no grep, no partial reads):

```bash
nix run .#spec-loader -- opencode-sidepanel-specs
# Verifies all 99 specs are present
```

### Sidepanel Implementation

PureScript/Halogen sidepanel (per specs 40-49):
- `src/sidepanel-ps/`: PureScript implementation
  - AppM monad, State management, Reducer
  - Router with Routing.Duplex
  - Dashboard component
  - Utilities (Time, Currency, Keyboard)
  - API types (JSON-RPC 2.0)
  - Theme system with PRISM colors
- Uses PRISM color system for theming
- Integrates with opencode-dev

**Status:** See `docs/IMPLEMENTATION_STATUS.md` for complete progress tracking.

### PRISM Color System

Formally verified color science:
- `PRISM/prism-color-core/haskell/`: Haskell implementation
- `PRISM/prism-color-core/lean4/`: Lean4 proofs
- WCAG accessibility guaranteed

## Development Standards

This workspace uses Cursor rules and skills to enforce development standards:

### Rules (`.cursor/rules/`)

Rules reference proven implementations:
- **core-principles.mdc**: Accuracy > Speed, Code is Truth (see `Rules.Core`)
- **type-system.mdc**: Types describe, code is truth (see `Rules.TypeSafety`)
- **file-reading-protocol.mdc**: Complete reads only (see `Rules.FileReading`)

### Skills (`.cursor/skills/`)

- **deterministic-coder**: MANDATORY for ALL code modifications
- **exploratory-architect**: MANDATORY for ALL architecture design tasks
- **expert-researcher**: For research and analysis tasks

## Getting Started

### Quick Start

1. **Set up environment** (see `docs/SETUP.md` for details):
   ```bash
   # WSL2 + Nix (recommended for Windows)
   wsl --install
   # Then in WSL2:
   sh <(curl -L https://nixos.org/nix/install) --daemon
   ```

2. **Enter dev shell**:
   ```bash
   nix develop
   ```

3. **Build all packages**:
   ```bash
   nix build .#all-packages
   ```

4. **Verify everything**:
   ```bash
   # Linux/WSL2
   bash scripts/verify.sh
   
   # Windows PowerShell
   powershell scripts/verify.ps1
   
   # Or use Nix apps
   nix run .#verify-all
   ```

### Verification

```bash
# Check flake
nix flake check

# Build implementations
nix build .#rules-ps
nix build .#rules-hs
nix build .#rules-lean
nix build .#prism-color-core-hs
nix build .#prism-color-core-lean
nix build .#sidepanel-ps
nix build .#spec-loader-hs

# Run tests
nix run .#test-all

# Verify proofs
nix run .#check-rules

# Verify specs
nix run .#spec-loader -- opencode-sidepanel-specs
```

## Migration Goals

The `opencode-dev` project will be migrated to match `trtllm-serve-main` standards:
- Type safety (PureScript/Haskell/Lean4 where applicable)
- Nix-based reproducible builds
- Strict type checking
- Complete file reading protocol
- No banned constructs
- Comprehensive documentation
- **Proven correctness** (Lean4 proofs)
- **Spec-driven development** (all 99 specs implemented)

## Verification

Before any task completion, verify:
- [ ] All files read completely
- [ ] Dependency graph traced
- [ ] All instances fixed across codebase
- [ ] No banned constructs
- [ ] Types explicit
- [ ] Type checks pass
- [ ] Tests pass
- [ ] **Proofs check** (Lean4)
- [ ] **Specs verified** (all 99 present)
- [ ] Documentation updated
- [ ] Workspace clean
