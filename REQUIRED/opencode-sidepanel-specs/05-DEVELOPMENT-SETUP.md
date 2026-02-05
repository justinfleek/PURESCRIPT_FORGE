# 05-DEVELOPMENT-SETUP: Local Environment Setup Guide

## Overview

This guide walks through setting up a complete development environment for the OpenCode Sidepanel project. Following these steps ensures you have identical tooling to every other developer on the project.

**Time required:** ~15 minutes  
**Prerequisites:** macOS, Linux, or WSL2

---

## Step 1: Install Nix

Nix is our package manager and build system. It ensures reproducible environments.

### macOS / Linux

```bash
# Install Nix with flakes enabled
curl --proto '=https' --tlsv1.2 -sSf -L https://install.determinate.systems/nix | sh -s -- install

# Or the official installer (then enable flakes manually)
sh <(curl -L https://nixos.org/nix/install) --daemon
```

### Enable Flakes (if using official installer)

Create or edit `~/.config/nix/nix.conf`:

```ini
experimental-features = nix-command flakes
```

### Verify Installation

```bash
nix --version
# Should output: nix (Nix) 2.18.x or higher
```

---

## Step 2: Clone the Repository

```bash
# Clone via SSH (recommended)
git clone git@github.com:weyl-ai/opencode-sidepanel.git
cd opencode-sidepanel

# Or via HTTPS
git clone https://github.com/weyl-ai/opencode-sidepanel.git
cd opencode-sidepanel
```

---

## Step 3: Enter Development Shell

```bash
# This downloads and sets up all dependencies
# First run takes 5-10 minutes; subsequent runs are instant
nix develop

# You should see:
# 🚀 OpenCode Sidepanel Development Environment
#
# Available commands:
#   just dev     - Start development servers
#   just build   - Build all packages
#   just test    - Run all tests
#   just fmt     - Format all code
```

### What's Installed

After entering the shell, you have access to:

| Tool | Version | Purpose |
|------|---------|---------|
| `node` | 20.x | JavaScript runtime |
| `pnpm` | 8.x | Node package manager |
| `purs` | 0.15.x | PureScript compiler |
| `spago` | 0.21.x | PureScript build tool |
| `purs-tidy` | latest | PureScript formatter |
| `lean` | 4.5.x | Lean4 compiler |
| `lake` | latest | Lean4 build tool |
| `just` | latest | Command runner |
| `watchexec` | latest | File watcher |

---

## Step 4: Install Project Dependencies

```bash
# Install Node.js dependencies for bridge server
cd bridge
pnpm install
cd ..

# Install PureScript dependencies for frontend
cd frontend
spago install
cd ..

# Verify everything installed
just check-deps
```

### Expected Output

```
✓ Node modules installed (bridge)
✓ PureScript packages installed (frontend)
✓ All dependencies satisfied
```

---

## Step 5: Configure Venice API Key

The sidepanel requires a Venice API key for AI features.

### Get Your API Key

1. Go to https://venice.ai/dashboard
2. Navigate to API Keys
3. Create a new key with appropriate permissions
4. Copy the key (starts with `vk_`)

### Store the Key Securely

```bash
# Store in system keychain (recommended)
just store-api-key

# You'll be prompted:
# Enter Venice API key: vk_your_key_here
# ✓ API key stored securely
```

**Never** put your API key in:
- Environment variables
- Config files
- Source code
- Git commits

---

## Step 6: Configure OpenCode

The sidepanel is an OpenCode plugin. You need OpenCode installed.

### Install OpenCode

```bash
# If not already installed
go install github.com/opencode-ai/opencode@latest

# Verify
opencode version
```

### Configure Plugin

Create or edit `~/.config/opencode/opencode.json`:

```json
{
  "$schema": "https://opencode.ai/config.json",
  "plugin": ["opencode-sidepanel"],
  "mcp": {
    "lean-lsp": {
      "type": "local",
      "command": "lean-lsp-mcp",
      "args": ["--transport", "stdio"]
    }
  },
  "sidepanel": {
    "port": 8765,
    "autoOpen": true,
    "theme": "dark"
  }
}
```

---

## Step 7: Start Development Servers

```bash
# Start all services in development mode
just dev

# This starts:
# - Bridge server on localhost:8765
# - PureScript compiler in watch mode
# - Opens browser to sidepanel
```

### What Happens

1. Bridge server starts, connecting to OpenCode
2. PureScript builds frontend
3. Browser opens to `http://localhost:8765`
4. File watchers start for hot reload

### Verify It's Working

You should see:
- Terminal: "Bridge server listening on :8765"
- Browser: Sidepanel dashboard with "Disconnected" status (normal until OpenCode runs)

---

## Step 8: Run OpenCode with Sidepanel

In a **separate terminal**:

```bash
# Enter the project directory with nix shell
cd /path/to/opencode-sidepanel
nix develop

# Start OpenCode with sidepanel
opencode --serve

# Or in any project
cd /your/project
opencode --serve
```

### Verify Integration

1. Browser sidepanel should show "Connected"
2. Diem balance should appear (if API key configured)
3. Countdown timer should be running

---

## Optional: Direnv Integration

For automatic shell activation when entering the directory:

### Install direnv

```bash
# macOS
brew install direnv

# Linux
nix profile install nixpkgs#direnv
```

### Configure Shell

Add to `~/.bashrc` or `~/.zshrc`:

```bash
eval "$(direnv hook bash)"  # or zsh
```

### Enable for Project

```bash
cd opencode-sidepanel
echo "use flake" > .envrc
direnv allow
```

Now entering the directory automatically activates the Nix shell.

---

## Troubleshooting

### "nix: command not found"

Nix wasn't installed correctly or shell wasn't restarted.

```bash
# Try restarting shell
exec $SHELL

# Or source nix
. /nix/var/nix/profiles/default/etc/profile.d/nix-daemon.sh
```

### "purs: command not found" inside nix develop

Flake might be corrupted. Try:

```bash
nix flake update
nix develop
```

### "spago install" fails with network error

Likely a registry issue. Try:

```bash
# Clear spago cache
rm -rf ~/.cache/spago
rm -rf frontend/.spago

# Retry
cd frontend && spago install
```

### Bridge server won't start

Port 8765 might be in use:

```bash
# Find what's using the port
lsof -i :8765

# Kill it or use different port
just dev -- --port 8766
```

### PureScript compilation errors

If you see type errors after pulling:

```bash
# Clean and rebuild
cd frontend
rm -rf output .spago
spago install
spago build
```

### "keytar" native module fails

Missing build tools:

```bash
# Should be automatic in nix develop, but if not:
pnpm rebuild keytar
```

### Lean4 not found

Lean might not be in PATH:

```bash
# Verify in nix shell
which lean
echo $LEAN_PATH

# Should show paths inside /nix/store
```

---

## IDE Setup

### VS Code / Cursor

Recommended extensions:
- `PureScript IDE` - PureScript language support
- `Nix IDE` - Nix language support
- `Lean 4` - Lean4 support

Settings for PureScript:

```json
{
  "purescript.addNpmPath": true,
  "purescript.buildCommand": "spago build --purs-args --json-errors"
}
```

### Neovim

Recommended plugins:
- `purescript-vim` or LSP via `purescript-language-server`
- `lean.nvim` for Lean4 support

```lua
-- LSP configuration
require'lspconfig'.purescriptls.setup{}
require'lspconfig'.lean4.setup{}
```

---

## Verification Checklist

Run through this checklist to verify your setup:

```bash
# All should succeed
just check-deps        # Dependencies installed
just build             # Project builds
just test              # Tests pass
just dev               # Dev server starts

# In separate terminal with OpenCode
opencode --serve       # OpenCode starts
# Browser should show "Connected"
```

- [ ] Nix installed and flakes enabled
- [ ] Repository cloned
- [ ] `nix develop` enters shell with all tools
- [ ] Bridge server starts on :8765
- [ ] PureScript compiles without errors
- [ ] Venice API key stored
- [ ] OpenCode configured with plugin
- [ ] Sidepanel connects to OpenCode

---

## Next Steps

1. Read `01-EXECUTIVE-SUMMARY.md` to understand the project
2. Read `02-SYSTEM-ARCHITECTURE.md` to understand how pieces fit together
3. Read `08-DEVELOPMENT-WORKFLOW.md` for day-to-day workflow
4. Start on assigned Phase 1 task

---

## Getting Help

- **Stuck on setup?** Check #sidepanel-dev in Slack
- **Bug in docs?** File an issue with "docs:" prefix
- **Nix questions?** Check NixOS Discourse or #nix channel

---

*"A proper setup is worth an hour. An improper setup costs days."*
