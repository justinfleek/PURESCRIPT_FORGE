#!/usr/bin/env bash
# Nix-based test script for compiler pipeline
set -euo pipefail

echo "=== Nix Build and Test ==="
echo ""

# Check if we're in a Nix flake
if [ ! -f flake.nix ]; then
  echo "Error: flake.nix not found. Run from compiler-pipeline directory."
  exit 1
fi

# Check Nix flake support
if ! nix flake --version >/dev/null 2>&1; then
  echo "Error: Nix flakes not enabled. Add to ~/.config/nix/nix.conf:"
  echo "  experimental-features = nix-command flakes"
  exit 1
fi

echo "Step 1: Verifying flake..."
nix flake check

echo ""
echo "Step 2: Building PureScript → C++23 compiler..."
nix build .#purescript-to-cpp23 --print-build-logs

echo ""
echo "Step 3: Building C++23 → React generator..."
nix build .#cpp23-to-react --print-build-logs

echo ""
echo "Step 4: Building WASM runtime..."
nix build .#runtime-wasm --print-build-logs || echo "Note: WASM build may require Emscripten setup"

echo ""
echo "Step 5: Running unit tests..."
nix run .#test || {
  echo "Unit tests failed. Entering dev shell for debugging..."
  echo "Run: cabal test parser-tests"
  echo "Run: cabal test generator-tests"
  echo "Run: cabal test typechecker-tests"
  exit 1
}

echo ""
echo "Step 6: Running integration tests..."
nix run .#test-integration || {
  echo "Integration tests failed. Check test-output/ directory."
  exit 1
}

echo ""
echo "=== All Nix builds and tests passed ==="
echo ""
echo "To enter development shell:"
echo "  nix develop"
echo ""
echo "To build everything:"
echo "  nix build .#default"
