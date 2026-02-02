# Nix Build and Test Guide

## Quick Start

**Note:** The compiler pipeline is integrated into the root `flake.nix` using aleph-continuity modules.

```bash
# Build compiler pipeline
nix build .#compiler-pipeline

# Build individual components
nix build .#compiler-pipeline-purescript-to-cpp23
nix build .#compiler-pipeline-cpp23-to-react
nix build .#compiler-pipeline-runtime-wasm

# Run all tests
nix run .#compiler-pipeline-test-all

# Run unit tests
nix run .#compiler-pipeline-test

# Run integration tests
nix run .#compiler-pipeline-test-integration

# Enter development shell
nix develop
```

## Prerequisites

### Enable Nix Flakes

Add to `~/.config/nix/nix.conf` (or `/etc/nix/nix.conf`):

```
experimental-features = nix-command flakes ca-derivations
```

### Windows Users

Nix on Windows requires:
- **WSL2** (recommended), OR
- **Native Nix** (experimental)

For WSL2, run commands from WSL terminal. PowerShell scripts will detect WSL automatically.

## Build Commands

### Individual Components

```bash
# PureScript → C++23 compiler
nix build .#purescript-to-cpp23

# C++23 → React generator
nix build .#cpp23-to-react

# WASM runtime
nix build .#runtime-wasm
```

### All Components

```bash
nix build .#default
```

Build outputs are in `result/bin/`:

```bash
ls -la result/bin/
# purescript-to-cpp23
# cpp23-to-react
```

## Test Commands

### Unit Tests

```bash
# Run all unit tests (parser, generator, typechecker)
nix run .#test
```

### Integration Tests

```bash
# Test full pipeline (PureScript → C++23 → React)
nix run .#test-integration
```

### All Tests

```bash
# Run unit + integration tests
nix run .#test-all
```

## Development Shell

Enter a development environment with all tools:

```bash
nix develop
```

Inside the shell:

```bash
# Build with Cabal (Haskell)
cd purescript-to-cpp23
cabal build
cabal test

# Build C++ manually
cd ../cpp23-to-react
clang++ -std=c++23 -O2 -o cpp23-to-react src/*.cpp

# Run test scripts
./scripts/test-nix.sh  # Linux/macOS
# or
./scripts/test-nix.ps1 # Windows (WSL)
```

## Verification

### Check Flake Syntax

```bash
nix flake check
```

### Verify Builds

```bash
# Build and verify all packages
nix build .#purescript-to-cpp23
nix build .#cpp23-to-react
nix build .#runtime-wasm

# Check binaries exist
ls -la result/bin/
```

### Run Checks

```bash
# All checks (builds + tests)
nix flake check
```

## Troubleshooting

### Build Failures

**Haskell dependencies missing:**
```bash
# Enter dev shell and build manually
nix develop
cd purescript-to-cpp23
cabal build
```

**C++ compilation errors:**
```bash
# Check Clang version
clang++ --version  # Should be 17+

# Build manually to see full error
cd cpp23-to-react
clang++ -std=c++23 -v src/*.cpp
```

**Emscripten not found:**
```bash
# WASM build requires Emscripten
# Install in dev shell:
nix develop
emcc --version
```

### Test Failures

**Unit tests fail:**
```bash
# Run tests manually with verbose output
nix develop
cd purescript-to-cpp23
cabal test parser-tests --test-show-details=direct
cabal test generator-tests --test-show-details=direct
cabal test typechecker-tests --test-show-details=direct
```

**Integration tests fail:**
```bash
# Check test output directory
ls -la test-output/
cat test-output/cpp23/*.hpp
cat test-output/react/*.tsx
```

### Flake Errors

**"experimental-features" not enabled:**
```bash
# Add to ~/.config/nix/nix.conf:
echo "experimental-features = nix-command flakes" >> ~/.config/nix/nix.conf
```

**Lock file out of date:**
```bash
nix flake update
nix flake lock
```

## CI/CD Integration

### GitHub Actions Example

```yaml
name: Build and Test

on: [push, pull_request]

jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - uses: cachix/install-nix-action@v20
        with:
          nix_path: nixpkgs=channel:nixos-unstable
      - run: nix flake check
      - run: nix build .#default
      - run: nix run .#test-all
```

## Package Structure

```
flake.nix
├── packages
│   ├── purescript-to-cpp23  (Haskell/Cabal)
│   ├── cpp23-to-react        (C++/Clang)
│   ├── runtime-wasm          (C++/Emscripten)
│   └── default               (all packages)
├── apps
│   ├── test                  (unit tests)
│   ├── test-integration      (integration tests)
│   └── test-all              (all tests)
├── devShells.default         (development environment)
└── checks                    (build + test verification)
```

## Next Steps

- See `TESTING.md` for detailed test documentation
- See `BUILD_AND_TEST.md` for alternative build methods (Buck2, manual)
- See `QUICK_START.md` for quick testing commands
