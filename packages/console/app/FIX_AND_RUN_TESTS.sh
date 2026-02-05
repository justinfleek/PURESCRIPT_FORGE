#!/usr/bin/env bash
# Fix test dependencies and run tests

set -e

echo "=== Fixing Test Dependencies ==="
echo ""

cd /mnt/c/Users/justi/Desktop/CODER/packages/console/app

# Step 1: Build console-core-ps
echo "Step 1: Building console-core-ps..."
cd /mnt/c/Users/justi/Desktop/CODER
nix build .#console-core-ps --no-link --print-build-logs 2>&1 | tail -20 || {
  echo "Warning: console-core-ps build may have issues, but continuing..."
}

# Step 2: Link console-core
echo ""
echo "Step 2: Linking console-core..."
cd packages/console/app
mkdir -p .spago

# Try to get the output path
CORE_OUTPUT=$(nix build .#console-core-ps --no-link --print-out-paths 2>/dev/null || echo "")

if [ -n "$CORE_OUTPUT" ] && [ -d "$CORE_OUTPUT/output" ]; then
  echo "Linking: $CORE_OUTPUT/output -> .spago/console-core"
  rm -f .spago/console-core
  ln -sf "$CORE_OUTPUT/output" .spago/console-core
  echo "✓ Linked console-core"
else
  echo "⚠ Warning: Could not find console-core output"
  echo "  Try: nix build .#console-core-ps"
fi

# Step 3: Install dependencies
echo ""
echo "Step 3: Installing test dependencies..."
export PATH=$HOME/.nix-profile/bin:$PATH
spago -x test.dhall install

echo ""
echo "=== Running Tests ==="
echo ""
echo "Note: Some tests may fail due to missing Sidepanel.Utils modules"
echo "These will be fixed in a follow-up"
echo ""

# Run tests - they'll show what's actually broken
spago -x test.dhall test 2>&1 | head -100

echo ""
echo "=== Test Run Complete ==="
echo ""
echo "Next steps:"
echo "1. Fix Sidepanel.Utils imports (modules don't exist in this package)"
echo "2. Fix Console.Core imports (need console-core-ps built)"
echo "3. Add missing packages (string-replacement)"
