#!/usr/bin/env bash
# Agent Quick Start Script
# One-command setup and verification for AI agents

set -e

echo "════════════════════════════════════════════════════════════════"
echo "  PURESCRIPT_FORGE Agent Quick Start"
echo "════════════════════════════════════════════════════════════════"
echo ""

# Check if Nix is installed
if ! command -v nix &> /dev/null; then
    echo "❌ Nix not found. Installing..."
    echo ""
    echo "For WSL2/Windows:"
    echo "  wsl --install"
    echo "  sh <(curl -L https://nixos.org/nix/install) --daemon"
    echo ""
    echo "For Linux/macOS:"
    echo "  sh <(curl -L https://nixos.org/nix/install) --daemon"
    echo ""
    echo "Then enable flakes:"
    echo "  mkdir -p ~/.config/nix"
    echo "  echo 'experimental-features = nix-command flakes' >> ~/.config/nix/nix.conf"
    exit 1
fi

echo "✅ Nix found: $(nix --version)"
echo ""

# Check if we're in the right directory
if [ ! -f "flake.nix" ]; then
    echo "❌ flake.nix not found. Are you in the FORGE directory?"
    echo "   Current directory: $(pwd)"
    exit 1
fi

echo "✅ In FORGE workspace"
echo ""

# Enter dev shell and run verification
echo "📦 Entering Nix development shell..."
echo "   (First run may take 5-10 minutes to download dependencies)"
echo ""

nix develop --command bash <<'DEVSHELL'
    echo ""
    echo "════════════════════════════════════════════════════════════════"
    echo "  Development Shell Active"
    echo "════════════════════════════════════════════════════════════════"
    echo ""
    
    # Verify tools
    echo "🔧 Verifying tools..."
    echo "   PureScript: $(purs --version 2>/dev/null || echo 'not found')"
    echo "   Haskell: $(ghc --version 2>/dev/null | head -1 || echo 'not found')"
    echo "   Lean4: $(lean --version 2>/dev/null || echo 'not found')"
    echo "   Node.js: $(node --version 2>/dev/null || echo 'not found')"
    echo ""
    
    # Quick build test
    echo "🔨 Testing build system..."
    if nix build .#rules-ps --no-link 2>&1 | head -5; then
        echo "   ✅ PureScript builds successfully"
    else
        echo "   ⚠️  Build test failed (may need flake update)"
    fi
    
    echo ""
    echo "════════════════════════════════════════════════════════════════"
    echo "  Quick Start Complete"
    echo "════════════════════════════════════════════════════════════════"
    echo ""
    echo "Next steps:"
    echo "  1. Build all packages:  nix build .#all-packages"
    echo "  2. Run tests:           nix run .#test-all"
    echo "  3. Verify system:       nix run .#verify-all"
    echo "  4. Start bridge server: cd src/bridge-server-ps && npm install && spago build && node output/Bridge.Main/index.js"
    echo ""
    echo "For full guide, see: AGENT_SETUP_GUIDE.md"
    echo ""
DEVSHELL
