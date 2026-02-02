# Agent Setup Guide: Running PURESCRIPT_FORGE System

## Quick Start for Agents

This guide provides the minimal setup required for AI agents to build, test, and run the PURESCRIPT_FORGE system.

---

## Prerequisites

### Required: Nix Package Manager

**Windows (Recommended):**
```powershell
# Install WSL2
wsl --install

# Then in WSL2:
sh <(curl -L https://nixos.org/nix/install) --daemon

# Enable flakes
mkdir -p ~/.config/nix
echo "experimental-features = nix-command flakes" >> ~/.config/nix/nix.conf
```

**Linux/macOS:**
```bash
sh <(curl -L https://nixos.org/nix/install) --daemon
mkdir -p ~/.config/nix
echo "experimental-features = nix-command flakes" >> ~/.config/nix/nix.conf
```

**Verify:**
```bash
nix --version  # Should show 2.18+
nix flake --version
```

---

## Step 1: Enter Development Shell

```bash
# Navigate to workspace
cd /mnt/c/Users/justi/Desktop/CODER  # WSL2 path (note: directory name unchanged)
# OR
cd ~/CODER  # If cloned to home (note: directory name unchanged)

# Enter Nix development shell (downloads all dependencies)
nix develop
```

**What this provides:**
- PureScript compiler (`purs`)
- PureScript build tool (`spago`)
- Haskell compiler (`ghc`, `cabal`)
- Lean4 compiler (`lean`)
- Node.js 20+ (`node`, `npm`, `pnpm`)
- All build tools and formatters

**First run:** Takes 5-10 minutes to download dependencies  
**Subsequent runs:** Instant (cached)

---

## Step 2: Build System

### Build All Packages
```bash
nix build .#all-packages
```

### Build Individual Components
```bash
# Bridge Server (PureScript)
nix build .#bridge-server-ps

# Sidepanel (PureScript/Halogen)
nix build .#sidepanel-ps

# Database Backend (Haskell)
nix build .#bridge-database-hs

# Analytics Backend (Haskell/DuckDB)
nix build .#bridge-analytics-hs

# OpenCode Types (PureScript)
nix build .#opencode-types-ps

# Validator (Haskell)
nix build .#opencode-validator-hs

# Proofs (Lean4)
nix build .#opencode-proofs-lean
```

### Build NEXUS Components
```bash
# All NEXUS packages
nix build .#nexus-all

# Individual NEXUS components
nix build .#semantic-cells-python
nix build .#nexus-agent-orchestrator-ps
nix build .#nexus-network-graph-ps
```

---

## Step 3: Run Development Servers

### Bridge Server (PureScript)
```bash
# From within nix develop shell
cd src/bridge-server-ps

# Install Node.js dependencies (first time only)
npm install

# Build PureScript
spago build

# Run bridge server
node output/Bridge.Main/index.js

# Or use the built package
nix run .#bridge-server-ps
```

**Expected output:**
```
Bridge server listening on :8765
WebSocket server ready
Database initialized
```

### Sidepanel (PureScript/Halogen)
```bash
cd src/sidepanel-ps

# Build
spago build

# Serve (requires build tool like parcel or webpack)
# See package.json scripts for exact command
```

---

## Step 4: Run Tests

### PureScript Tests
```bash
# Bridge Server tests
cd src/bridge-server-ps
spago test

# Sidepanel tests
cd src/sidepanel-ps
spago test
```

### Haskell Tests
```bash
# Database tests
cd src/bridge-database-hs
cabal test

# Validator tests
cd src/opencode-validator-hs
cabal test
```

### Lean4 Proof Verification
```bash
# Verify proofs compile
nix build .#opencode-proofs-lean
nix build .#nexus-proofs-lean

# Or manually
cd src/opencode-proofs-lean
lean --version
lake build
```

### Run All Tests
```bash
nix run .#test-all
```

---

## Step 5: Verification Commands

### Verify Flake Configuration
```bash
nix flake check
```

### Verify All Builds
```bash
nix run .#verify-all
```

### Verify Rules Implementations
```bash
nix run .#check-rules
```

### Validate OpenCode Code
```bash
nix run .#validate-opencode
```

### Verify Specs
```bash
nix run .#spec-loader -- opencode-sidepanel-specs
```

---

## Step 6: Formatting & Linting

### Format All Code
```bash
nix fmt
# OR
nix run .#formatter
```

### Lint
```bash
# PureScript
cd src/bridge-server-ps
spago format --check

# Haskell
cd src/bridge-database-hs
cabal format

# Nix
nix fmt
```

---

## Step 7: Type Checking

### PureScript Type Check
```bash
cd src/bridge-server-ps
spago build --no-build  # Type check only
```

### Haskell Type Check
```bash
cd src/bridge-database-hs
cabal build --ghc-options=-Werror
```

### Lean4 Proof Check
```bash
cd src/opencode-proofs-lean
lake build  # Compiles proofs
```

---

## Common Workflows

### Workflow 1: Make Code Changes
```bash
# 1. Enter dev shell
nix develop

# 2. Make changes to PureScript/Haskell/Lean4

# 3. Format
nix fmt

# 4. Type check
cd src/bridge-server-ps && spago build --no-build

# 5. Build
nix build .#bridge-server-ps

# 6. Test
spago test

# 7. Verify
nix flake check
```

### Workflow 2: Run Full System
```bash
# Terminal 1: Bridge Server
nix develop
cd src/bridge-server-ps
npm install
spago build
node output/Bridge.Main/index.js

# Terminal 2: Sidepanel (if separate)
cd src/sidepanel-ps
spago build
# Run dev server per package.json scripts

# Terminal 3: OpenCode (if available)
opencode --serve
```

### Workflow 3: Verify Before Commit
```bash
# 1. Format
nix fmt

# 2. Type check all
nix build .#all-packages

# 3. Run tests
nix run .#test-all

# 4. Verify proofs
nix build .#opencode-proofs-lean

# 5. Validate code
nix run .#validate-opencode

# 6. Check flake
nix flake check
```

---

## Environment Variables

### Bridge Server
```bash
export SIDEPANEL_PORT=8765
export SIDEPANEL_HOST=127.0.0.1
export VENICE_API_KEY=your-key-here  # Optional
export STORAGE_PATH=./data/bridge.db
export LOG_LEVEL=info
export LOG_FORMAT=pretty
```

### Create `.env` file (optional)
```bash
# In src/bridge-server-ps/
cat > .env <<EOF
VENICE_API_KEY=your-key-here
STORAGE_PATH=./data/bridge.db
LOG_LEVEL=info
EOF
```

---

## Health Checks

### Bridge Server Health
```bash
curl http://localhost:8765/health
# Expected: {"status":"ok"}
```

### WebSocket Test
```bash
# Using websocat (install: nix profile install nixpkgs#websocat)
websocat ws://localhost:8765/ws
# Send: {"jsonrpc":"2.0","method":"ping","id":1}
# Expected: {"jsonrpc":"2.0","result":"pong","id":1}
```

---

## Troubleshooting

### "nix: command not found"
```bash
# Restart shell or source Nix
. /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh
```

### "experimental-features" error
```bash
mkdir -p ~/.config/nix
echo "experimental-features = nix-command flakes" >> ~/.config/nix/nix.conf
```

### Build failures
```bash
# Update flake inputs
nix flake update

# Rebuild from scratch
nix develop --rebuild
```

### Port already in use
```bash
# Find process using port 8765
lsof -i :8765

# Kill it
kill -9 <PID>

# Or use different port
export SIDEPANEL_PORT=8766
```

### PureScript compilation errors
```bash
# Clear Spago cache
rm -rf ~/.cache/spago
rm -rf src/*/ps/.spago

# Rebuild
spago build
```

---

## Quick Reference

### Essential Commands
```bash
nix develop                    # Enter dev shell
nix build .#all-packages      # Build everything
nix run .#test-all            # Run all tests
nix fmt                        # Format all code
nix flake check                # Verify flake
nix run .#verify-all           # Full verification
```

### Development Commands
```bash
spago build                    # Build PureScript
spago test                     # Test PureScript
cabal build                    # Build Haskell
cabal test                     # Test Haskell
lake build                     # Build Lean4 proofs
```

### Verification Commands
```bash
nix run .#check-rules          # Verify rules
nix run .#validate-opencode    # Validate code
nix run .#spec-loader -- opencode-sidepanel-specs  # Verify specs
```

---

## System Architecture

### Components
- **Bridge Server** (PureScript): WebSocket server, state management
- **Sidepanel** (PureScript/Halogen): Frontend UI
- **Database** (Haskell): SQLite persistence
- **Analytics** (Haskell/DuckDB): Analytics queries
- **NEXUS** (Python/PureScript): Agent orchestration
- **Proofs** (Lean4): Formal verification

### Ports
- Bridge Server: `8765` (HTTP + WebSocket)
- NativeLink LRE: `50051` (if enabled)

---

## Next Steps

1. **Verify setup:** Run `nix run .#verify-all`
2. **Build system:** Run `nix build .#all-packages`
3. **Run tests:** Run `nix run .#test-all`
4. **Start development:** Make changes and verify with `nix flake check`

---

**Last Updated:** 2026-01-30  
**System Status:** ✅ All core components implemented and tested
