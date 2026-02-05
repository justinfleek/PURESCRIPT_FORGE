# Troubleshooting Test Execution

## Kill Stuck Nix Processes

If `nix develop` or `nix run` is stuck, kill stuck processes:

```bash
# In WSL
./KILL_NIX_PROCESSES.sh

# Or manually:
pkill -9 nix
pkill -9 nix-daemon
killall -9 nix-daemon
```

## Check for Stuck Processes

```bash
# Check what's running
ps aux | grep nix

# Check nix-daemon
pgrep -f nix-daemon
```

## Fix: Build console-core First

The `console-app-test` app depends on `console-core-ps` being built. Build it first:

```bash
# From project root
nix build .#console-core-ps

# Then run tests
nix run .#console-app-test
```

## Alternative: Simple Test Script

If the flake app isn't working, use this simple script:

```bash
# Create a simple test runner
cat > /tmp/run-tests.sh << 'EOF'
#!/usr/bin/env bash
set -e
cd /mnt/c/Users/justi/Desktop/CODER/packages/console/app
export PATH=$(nix-build -E 'with import <nixpkgs> {}; "${purescript}/bin:${spago}/bin:${nodejs_20}/bin"' --no-out-link)/bin:$PATH
spago -x test.dhall install
spago -x test.dhall test
EOF

chmod +x /tmp/run-tests.sh
/tmp/run-tests.sh
```

## Check Nix Evaluation

If `nix develop` is stuck evaluating, check what's happening:

```bash
# Check if it's actually working (look for CPU/network activity)
top
htop

# Or try with timeout
timeout 60 nix develop || echo "Timed out after 60 seconds"
```

## Nuclear Option: Restart Nix Daemon

```bash
# Stop nix-daemon
sudo systemctl stop nix-daemon  # If using systemd
# Or
killall -9 nix-daemon

# Clear nix cache (if needed)
nix-collect-garbage -d

# Restart nix-daemon
sudo systemctl start nix-daemon  # If using systemd
```
