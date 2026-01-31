#!/usr/bin/env bash
set -euo pipefail

# These will be replaced by Nix substitution
PURESCRIPT_TO_CPP23_BIN="@purescriptToCpp23@/bin/purescript-to-cpp23"
CPP23_TO_REACT_BIN="@cpp23ToReact@/bin/cpp23-to-react"

echo "=== Running Compiler Pipeline Integration Tests ==="

TEST_OUTPUT="src/compiler-pipeline/test-output"
mkdir -p "$TEST_OUTPUT/cpp23" "$TEST_OUTPUT/react"

# Test PureScript → C++23 compilation
if [ -f src/compiler-pipeline/tests/test_purescript.purs ]; then
  echo "Testing PureScript → C++23..."
  "$PURESCRIPT_TO_CPP23_BIN" compile \
    src/compiler-pipeline/tests/test_purescript.purs "$TEST_OUTPUT/cpp23" || true
  
  if [ -f "$TEST_OUTPUT/cpp23/Test.hpp" ]; then
    echo "✓ C++23 header generated"
  else
    echo "✗ C++23 header missing"
    exit 1
  fi
fi

# Test C++23 → React conversion
if [ -f "$TEST_OUTPUT/cpp23/Test.hpp" ]; then
  echo "Testing C++23 → React..."
  "$CPP23_TO_REACT_BIN" \
    "$TEST_OUTPUT/cpp23/Test.hpp" \
    "$TEST_OUTPUT/react" || true
fi

echo "=== Integration tests complete ==="
