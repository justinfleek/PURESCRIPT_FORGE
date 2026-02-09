# Quick Start: Build and Test

## Windows (PowerShell)

### Option 1: Quick Test Script

```powershell
# Run quick test
.\scripts\test-quick.ps1

# Run full test suite
.\scripts\run-tests.ps1
```

### Option 2: Manual Build and Test

```powershell
# 1. Build PureScript → C++23 compiler
cd purescript-to-cpp23
cabal build
cabal install --installdir=..\bin

# 2. Test compilation
cd ..
mkdir test-output\cpp23 -Force
.\bin\purescript-to-cpp23.exe compile tests\test_purescript.purs test-output\cpp23

# 3. Verify output
Get-ChildItem test-output\cpp23\ -Recurse
```

## Linux/macOS

### Option 1: Quick Test Script

```bash
# Make scripts executable
chmod +x scripts/*.sh

# Run quick test
./scripts/test-quick.sh

# Run full test suite
./scripts/test-all.sh
```

### Option 2: Manual Build and Test

```bash
# 1. Build PureScript → C++23 compiler
cd purescript-to-cpp23
cabal build
cabal install --installdir=../bin

# 2. Test compilation
cd ..
mkdir -p test-output/cpp23
./bin/purescript-to-cpp23 compile tests/test_purescript.purs test-output/cpp23

# 3. Verify output
ls -la test-output/cpp23/
cat test-output/cpp23/Test.hpp
```

## Using Nix (All Platforms)

```bash
# Build everything
nix build .#compiler-pipeline

# Test
./result/bin/purescript-to-cpp23 compile tests/test_purescript.purs /tmp/test-output
```

## Expected Output

After running the test, you should see:

1. **C++23 Header** (`Test.hpp`):
   ```cpp
   #pragma once
   namespace Test { ... }
   ```

2. **C++23 Implementation** (`Test.cpp`):
   ```cpp
   #include "Test.hpp"
   namespace Test { ... }
   ```

3. **React Component** (`Test.tsx`):
   ```tsx
   import * as React from 'react';
   export const Test: React.FC = ...
   ```

## Troubleshooting

### "Command not found"
- Make sure you've built the compiler: `cabal build`
- Check the binary exists: `ls bin/purescript-to-cpp23` or `dir bin\purescript-to-cpp23.exe`

### "Parse error"
- Check your PureScript syntax matches the parser
- See `tests/test_purescript.purs` for examples

### "Build failed"
- Install dependencies: `cabal install --dependencies-only`
- Check GHC version: `ghc --version` (should be 9.6+)

## Next Steps

1. ✅ Build successful? → Try your own PureScript code
2. ✅ Tests pass? → Check generated output quality
3. ✅ Everything works? → Run benchmarks: `cabal bench benchmarks`
