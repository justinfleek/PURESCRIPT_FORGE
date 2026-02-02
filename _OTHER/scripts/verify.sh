#!/usr/bin/env bash
# Verification script for FORGE workspace

set -euo pipefail

echo "════════════════════════════════════════════════════════════════"
echo "  FORGE Workspace Verification"
echo "════════════════════════════════════════════════════════════════"
echo ""

# Check Nix is available
if ! command -v nix &> /dev/null; then
    echo "❌ Nix not found. Please install Nix first."
    echo "   See docs/SETUP.md for instructions"
    exit 1
fi

echo "✅ Nix found: $(nix --version)"
echo ""

# Verify flake
echo "Verifying flake..."
nix flake check || {
    echo "❌ Flake check failed"
    exit 1
}
echo "✅ Flake check passed"
echo ""

# Build PureScript rules
echo "Building PureScript rules..."
nix build .#rules-ps || {
    echo "❌ PureScript build failed"
    exit 1
}
echo "✅ PureScript rules built"
echo ""

# Build Haskell rules
echo "Building Haskell rules..."
nix build .#rules-hs || {
    echo "❌ Haskell build failed"
    exit 1
}
echo "✅ Haskell rules built"
echo ""

# Build Lean4 proofs
echo "Building Lean4 proofs..."
nix build .#rules-lean || {
    echo "❌ Lean4 proofs failed"
    exit 1
}
echo "✅ Lean4 proofs verified"
echo ""

# Run tests
echo "Running property tests..."
nix build .#rules-hs.tests.rules-test || {
    echo "❌ Property tests failed"
    exit 1
}
echo "✅ Property tests passed"
echo ""

echo "════════════════════════════════════════════════════════════════"
echo "  All verifications passed!"
echo "════════════════════════════════════════════════════════════════"
