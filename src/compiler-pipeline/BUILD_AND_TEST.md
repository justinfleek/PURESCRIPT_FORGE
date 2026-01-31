# Build and Test Guide

## Quick Start

### Windows (PowerShell)

```powershell
# Build with Nix (if available)
nix build .#compiler-pipeline

# Or build manually
cd purescript-to-cpp23
cabal build
cabal install --installdir=../bin

# Test the build
cd ..
.\bin\purescript-to-cpp23 compile tests\test_purescript.purs test-output\cpp23
```

### Linux/macOS

```bash
# Quick test
./scripts/test-quick.sh

# Full test suite
./scripts/test-all.sh

# Integration tests
./scripts/test-integration.sh
```

## Build Verification

### Step 1: Verify Binaries Exist

```bash
# Check PureScript → C++23 compiler
ls -la bin/purescript-to-cpp23
# or
ls -la result/bin/purescript-to-cpp23

# Check C++23 → React generator
ls -la bin/cpp23-to-react
# or
ls -la result/bin/cpp23-to-react
```

### Step 2: Test Compilation

```bash
# Create output directory
mkdir -p test-output/cpp23

# Compile test file
./bin/purescript-to-cpp23 compile tests/test_purescript.purs test-output/cpp23

# Verify output
ls -la test-output/cpp23/
cat test-output/cpp23/Test.hpp
cat test-output/cpp23/Test.cpp
```

### Step 3: Test React Generation

```bash
# Generate React code
mkdir -p test-output/react
./bin/cpp23-to-react test-output/cpp23/Test.cpp test-output/react

# Verify output
ls -la test-output/react/
cat test-output/react/Test.tsx
```

## Running Tests

### Unit Tests

```bash
cd purescript-to-cpp23
cabal test parser-tests
cabal test generator-tests
cabal test typechecker-tests
```

### All Tests

```bash
cd purescript-to-cpp23
cabal test
```

### Benchmarks

```bash
cd purescript-to-cpp23
cabal bench benchmarks
```

## Expected Output

### Input: `tests/test_purescript.purs`
```purescript
module Test where
x = 42;
```

### Output: `Test.hpp`
```cpp
#pragma once
#include <cstdint>

namespace Test {
  inline auto x() -> std::int64_t {
    return 42;
  }
}
```

### Output: `Test.tsx`
```tsx
import * as React from 'react';

export const Test: React.FC = () => {
  return <div>{42}</div>;
};
```

## Troubleshooting

### Build Fails

1. **Check dependencies**:
   ```bash
   cabal install --dependencies-only
   ```

2. **Clean and rebuild**:
   ```bash
   cabal clean
   cabal build
   ```

3. **Check GHC version**:
   ```bash
   ghc --version
   # Should be 9.6+
   ```

### Tests Fail

1. **Check test files exist**:
   ```bash
   ls -la tests/
   ```

2. **Run tests with verbose output**:
   ```bash
   cabal test --test-show-details=direct
   ```

3. **Check generated output**:
   ```bash
   cat test-output/cpp23/Test.hpp
   ```

## Next Steps

After successful build and test:

1. **Review generated code** in `test-output/`
2. **Run benchmarks** to verify performance
3. **Check test coverage** with `cabal test --enable-coverage`
4. **Try your own PureScript code** in `tests/`
