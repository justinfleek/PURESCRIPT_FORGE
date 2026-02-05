#!/usr/bin/env bash
# Fix test dependencies - build console-core and link it

set -e

echo "Step 1: Building console-core-ps..."
cd /mnt/c/Users/justi/Desktop/CODER
nix build .#console-core-ps --no-link --print-build-logs || {
  echo "Warning: console-core-ps build failed, but continuing..."
}

echo ""
echo "Step 2: Linking console-core output..."
cd packages/console/app
mkdir -p .spago

# Get the path to console-core output
CORE_OUTPUT=$(nix build .#console-core-ps --no-link --print-out-paths 2>/dev/null || echo "")

if [ -n "$CORE_OUTPUT" ] && [ -d "$CORE_OUTPUT/output" ]; then
  echo "Linking console-core from: $CORE_OUTPUT/output"
  ln -sf "$CORE_OUTPUT/output" .spago/console-core || true
else
  echo "Warning: console-core output not found, tests may fail"
  echo "Try: nix build .#console-core-ps"
fi

echo ""
echo "Step 3: Installing test dependencies..."
export PATH=$HOME/.nix-profile/bin:$PATH
spago -x test.dhall install

echo ""
echo "Done! Now run: spago -x test.dhall test"
