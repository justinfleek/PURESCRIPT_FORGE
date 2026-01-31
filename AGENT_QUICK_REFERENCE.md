# Agent Quick Reference Card

## One-Command Setup

```bash
# From workspace root
bash scripts/agent-quick-start.sh
```

---

## Essential Commands

### Setup
```bash
nix develop                    # Enter dev shell (5-10 min first time)
```

### Build
```bash
nix build .#all-packages       # Build everything
nix build .#bridge-server-ps   # Build bridge server
nix build .#sidepanel-ps        # Build sidepanel
```

### Test
```bash
nix run .#test-all             # Run all tests
cd src/bridge-server-ps && spago test
```

### Verify
```bash
nix flake check                # Verify flake configuration
nix run .#verify-all           # Full system verification
nix run .#check-rules          # Verify rules implementations
```

### Format
```bash
nix fmt                        # Format all code
```

---

## Run Bridge Server

```bash
# Terminal 1: Enter dev shell
nix develop

# Terminal 2: Build and run bridge server
cd src/bridge-server-ps
npm install                    # First time only
spago build
node output/Bridge.Main/index.js
```

**Expected output:**
```
Bridge server listening on :8765
WebSocket server ready
```

**Health check:**
```bash
curl http://localhost:8765/health
```

---

## Run Sidepanel

```bash
cd src/sidepanel-ps
spago build
# Then serve via your preferred method (parcel, webpack, etc.)
```

---

## Environment Variables

```bash
export SIDEPANEL_PORT=8765
export VENICE_API_KEY=your-key-here  # Optional
export STORAGE_PATH=./data/bridge.db
export LOG_LEVEL=info
```

---

## Troubleshooting

| Issue | Solution |
|-------|----------|
| `nix: command not found` | Install Nix (see AGENT_SETUP_GUIDE.md) |
| `experimental-features` error | Enable flakes in `~/.config/nix/nix.conf` |
| Port 8765 in use | `lsof -i :8765` then `kill -9 <PID>` |
| Build failures | `nix flake update` then retry |

---

## File Locations

| Component | Path |
|-----------|------|
| Bridge Server | `src/bridge-server-ps/` |
| Sidepanel | `src/sidepanel-ps/` |
| Database | `src/bridge-database-hs/` |
| Tests | `src/*/test/` |
| Proofs | `src/opencode-proofs-lean/` |

---

## Verification Checklist

Before considering system "ready":
- [ ] `nix develop` succeeds
- [ ] `nix build .#all-packages` succeeds
- [ ] `nix run .#test-all` passes
- [ ] `nix flake check` passes
- [ ] Bridge server starts and responds to `/health`
- [ ] WebSocket accepts connections

---

**Full Guide:** See `AGENT_SETUP_GUIDE.md` for detailed instructions.
