#!/bin/bash
# Verification Script - Phase 1: Compilation Verification
# Verifies all code compiles correctly

set -e

echo "════════════════════════════════════════════════════════════════"
echo "  Phase 1: Compilation Verification"
echo "════════════════════════════════════════════════════════════════"
echo ""

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Track results
PURESCRIPT_PASSED=0
PURESCRIPT_FAILED=0
HASKELL_PASSED=0
HASKELL_FAILED=0
LEAN4_PASSED=0
LEAN4_FAILED=0

# Function to print status
print_status() {
    if [ $1 -eq 0 ]; then
        echo -e "${GREEN}✓${NC} $2"
    else
        echo -e "${RED}✗${NC} $2"
    fi
}

# Function to check if command exists
check_command() {
    if ! command -v $1 &> /dev/null; then
        echo -e "${RED}Error: $1 not found${NC}"
        echo "Please install $1 to continue verification"
        exit 1
    fi
}

echo "Checking required tools..."
check_command "spago"
check_command "cabal"
check_command "lean"
echo ""

# ============================================================================
# PureScript Verification
# ============================================================================
echo "────────────────────────────────────────────────────────────────"
echo "  PureScript Verification"
echo "────────────────────────────────────────────────────────────────"
echo ""

# Bridge Server PureScript
echo "Verifying bridge-server-ps..."
cd src/bridge-server-ps
if spago build 2>&1 | tee /tmp/purescript-build.log; then
    print_status 0 "bridge-server-ps compiled successfully"
    PURESCRIPT_PASSED=$((PURESCRIPT_PASSED + 1))
else
    print_status 1 "bridge-server-ps compilation failed"
    PURESCRIPT_FAILED=$((PURESCRIPT_FAILED + 1))
    echo "Build errors:"
    cat /tmp/purescript-build.log | grep -i error || true
fi
cd ../..

# OpenCode Plugin PureScript
if [ -d "src/opencode-plugin-ps" ]; then
    echo ""
    echo "Verifying opencode-plugin-ps..."
    cd src/opencode-plugin-ps
    if spago build 2>&1 | tee /tmp/purescript-plugin-build.log; then
        print_status 0 "opencode-plugin-ps compiled successfully"
        PURESCRIPT_PASSED=$((PURESCRIPT_PASSED + 1))
    else
        print_status 1 "opencode-plugin-ps compilation failed"
        PURESCRIPT_FAILED=$((PURESCRIPT_FAILED + 1))
        echo "Build errors:"
        cat /tmp/purescript-plugin-build.log | grep -i error || true
    fi
    cd ../..
fi

# ============================================================================
# Haskell Verification
# ============================================================================
echo ""
echo "────────────────────────────────────────────────────────────────"
echo "  Haskell Verification"
echo "────────────────────────────────────────────────────────────────"
echo ""

# Bridge Database Haskell
echo "Verifying bridge-database-hs..."
cd src/bridge-database-hs
if cabal build 2>&1 | tee /tmp/haskell-build.log; then
    print_status 0 "bridge-database-hs compiled successfully"
    HASKELL_PASSED=$((HASKELL_PASSED + 1))
else
    print_status 1 "bridge-database-hs compilation failed"
    HASKELL_FAILED=$((HASKELL_FAILED + 1))
    echo "Build errors:"
    cat /tmp/haskell-build.log | grep -i error || true
fi
cd ../..

# Bridge Analytics Haskell
if [ -d "src/bridge-analytics-hs" ]; then
    echo ""
    echo "Verifying bridge-analytics-hs..."
    cd src/bridge-analytics-hs
    if cabal build 2>&1 | tee /tmp/haskell-analytics-build.log; then
        print_status 0 "bridge-analytics-hs compiled successfully"
        HASKELL_PASSED=$((HASKELL_PASSED + 1))
    else
        print_status 1 "bridge-analytics-hs compilation failed"
        HASKELL_FAILED=$((HASKELL_FAILED + 1))
        echo "Build errors:"
        cat /tmp/haskell-analytics-build.log | grep -i error || true
    fi
    cd ../..
fi

# ============================================================================
# Lean4 Verification
# ============================================================================
echo ""
echo "────────────────────────────────────────────────────────────────"
echo "  Lean4 Verification"
echo "────────────────────────────────────────────────────────────────"
echo ""

# Rules Lean4
echo "Verifying rules-lean..."
cd src/rules-lean
if lean --version > /dev/null 2>&1; then
    # Check if lakefile.lean exists
    if [ -f "lakefile.lean" ]; then
        if lake build 2>&1 | tee /tmp/lean-build.log; then
            print_status 0 "rules-lean compiled successfully"
            LEAN4_PASSED=$((LEAN4_PASSED + 1))
        else
            print_status 1 "rules-lean compilation failed"
            LEAN4_FAILED=$((LEAN4_FAILED + 1))
            echo "Build errors:"
            cat /tmp/lean-build.log | grep -i error || true
        fi
    else
        echo -e "${YELLOW}⚠${NC} No lakefile.lean found, skipping Lean4 build"
    fi
else
    echo -e "${YELLOW}⚠${NC} Lean4 not found, skipping verification"
fi
cd ../..

# ============================================================================
# Summary
# ============================================================================
echo ""
echo "════════════════════════════════════════════════════════════════"
echo "  Verification Summary"
echo "════════════════════════════════════════════════════════════════"
echo ""

TOTAL_PASSED=$((PURESCRIPT_PASSED + HASKELL_PASSED + LEAN4_PASSED))
TOTAL_FAILED=$((PURESCRIPT_FAILED + HASKELL_FAILED + LEAN4_FAILED))
TOTAL=$((TOTAL_PASSED + TOTAL_FAILED))

echo "PureScript:"
echo "  Passed: $PURESCRIPT_PASSED"
echo "  Failed: $PURESCRIPT_FAILED"
echo ""
echo "Haskell:"
echo "  Passed: $HASKELL_PASSED"
echo "  Failed: $HASKELL_FAILED"
echo ""
echo "Lean4:"
echo "  Passed: $LEAN4_PASSED"
echo "  Failed: $LEAN4_FAILED"
echo ""
echo "────────────────────────────────────────────────────────────────"
echo "Total: $TOTAL_PASSED passed, $TOTAL_FAILED failed"
echo "────────────────────────────────────────────────────────────────"

if [ $TOTAL_FAILED -eq 0 ]; then
    echo -e "${GREEN}✓ All verifications passed!${NC}"
    exit 0
else
    echo -e "${RED}✗ Some verifications failed${NC}"
    echo ""
    echo "Next steps:"
    echo "1. Review build errors above"
    echo "2. Fix compilation errors"
    echo "3. Re-run verification: ./scripts/verify-compilation.sh"
    exit 1
fi
