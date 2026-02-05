#!/usr/bin/env bash
# Kill stuck Nix processes

echo "Checking for Nix processes..."

# Find all nix processes
NIX_PIDS=$(ps aux | grep -E 'nix|nix-daemon' | grep -v grep | awk '{print $2}')

if [ -z "$NIX_PIDS" ]; then
  echo "No Nix processes found."
else
  echo "Found Nix processes:"
  ps aux | grep -E 'nix|nix-daemon' | grep -v grep
  
  echo ""
  echo "Killing Nix processes..."
  for pid in $NIX_PIDS; do
    echo "Killing PID $pid..."
    kill -9 $pid 2>/dev/null || true
  done
  
  echo "Done."
fi

# Also kill any stuck nix-daemon workers
echo ""
echo "Checking for nix-daemon workers..."
NIX_WORKER_PIDS=$(pgrep -f 'nix-daemon' || true)
if [ -n "$NIX_WORKER_PIDS" ]; then
  echo "Killing nix-daemon workers..."
  killall -9 nix-daemon 2>/dev/null || true
fi

echo ""
echo "All Nix processes killed."
