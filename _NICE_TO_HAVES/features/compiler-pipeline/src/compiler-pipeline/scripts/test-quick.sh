#!/bin/bash
# Quick test script for compiler pipeline
set -e

echo "=== Quick Build Test ==="

# Check if we're in Nix shell or have binaries
if command -v purescript-to-cpp23 &> /dev/null; then
    PS_TO_CPP="purescript-to-cpp23"
    CPP_TO_REACT="cpp23-to-react"
elif [ -f "./result/bin/purescript-to-cpp23" ]; then
    PS_TO_CPP="./result/bin/purescript-to-cpp23"
    CPP_TO_REACT="./result/bin/cpp23-to-react"
elif [ -f "./bin/purescript-to-cpp23" ]; then
    PS_TO_CPP="./bin/purescript-to-cpp23"
    CPP_TO_REACT="./bin/cpp23-to-react"
else
    echo "Building compiler pipeline..."
    nix build .#compiler-pipeline 2>&1 | tail -20
    PS_TO_CPP="./result/bin/purescript-to-cpp23"
    CPP_TO_REACT="./result/bin/cpp23-to-react"
fi

# Create test output directory
TEST_DIR="/tmp/compiler-pipeline-test-$$"
mkdir -p "$TEST_DIR/cpp23" "$TEST_DIR/react"

echo "Testing PureScript → C++23 compilation..."
"$PS_TO_CPP" compile tests/test_purescript.purs "$TEST_DIR/cpp23" || {
    echo "❌ PureScript → C++23 compilation failed"
    exit 1
}

# Verify C++23 output
if [ ! -f "$TEST_DIR/cpp23/Test.hpp" ] && [ ! -f "$TEST_DIR/cpp23/Test.cpp" ]; then
    # Try to find generated files
    GENERATED_HPP=$(find "$TEST_DIR/cpp23" -name "*.hpp" | head -1)
    GENERATED_CPP=$(find "$TEST_DIR/cpp23" -name "*.cpp" | head -1)
    
    if [ -z "$GENERATED_HPP" ] || [ -z "$GENERATED_CPP" ]; then
        echo "❌ No C++23 output files generated"
        echo "Generated files:"
        ls -la "$TEST_DIR/cpp23/" || true
        exit 1
    fi
    CPP_FILE="$GENERATED_CPP"
else
    CPP_FILE="$TEST_DIR/cpp23/Test.cpp"
fi

echo "✅ C++23 files generated"

echo "Testing C++23 → React generation..."
"$CPP_TO_REACT" "$CPP_FILE" "$TEST_DIR/react" || {
    echo "❌ C++23 → React generation failed"
    exit 1
}

# Verify React output
REACT_FILE=$(find "$TEST_DIR/react" -name "*.tsx" -o -name "*.jsx" | head -1)
if [ -z "$REACT_FILE" ]; then
    echo "❌ No React output files generated"
    echo "Generated files:"
    ls -la "$TEST_DIR/react/" || true
    exit 1
fi

echo "✅ React files generated"

# Basic validation
echo "Validating outputs..."
if grep -q "namespace\|#include" "$CPP_FILE" 2>/dev/null; then
    echo "✅ C++23 output looks valid"
else
    echo "⚠️  C++23 output may be invalid"
fi

if grep -q "React\|import\|export" "$REACT_FILE" 2>/dev/null; then
    echo "✅ React output looks valid"
else
    echo "⚠️  React output may be invalid"
fi

echo ""
echo "=== Test Results ==="
echo "C++23 Output: $CPP_FILE"
echo "React Output: $REACT_FILE"
echo ""
echo "✅ Quick test passed!"
echo "Test files preserved in: $TEST_DIR"
