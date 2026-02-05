# Quick Test Execution (Without Full Dev Shell)

If `nix develop` is taking too long, you can run tests directly without entering the full dev shell.

## Method 1: Direct Nix Command (Fastest)

Run spago test directly via Nix:

```bash
# From project root
nix run nixpkgs#spago -- -x packages/console/app/test.dhall test
```

Or from within `packages/console/app`:

```bash
cd packages/console/app
nix run nixpkgs#spago -- -x test.dhall test
```

## Method 2: Install Spago Locally (One-time Setup)

Install spago in your WSL environment:

```bash
# In WSL
nix profile install nixpkgs#spago
nix profile install nixpkgs#purescript

# Then you can use spago directly
cd /mnt/c/Users/justi/Desktop/CODER/packages/console/app
spago -x test.dhall install  # First time only
spago -x test.dhall test
```

## Method 3: Wait for nix develop (If It's Still Running)

If `nix develop` is still evaluating, it's likely downloading/evaluating dependencies. This can take:
- **5-15 minutes** on first run
- **1-3 minutes** on subsequent runs (if cached)

You can check if it's making progress by:
1. Opening another terminal and checking CPU/network usage
2. Looking for network activity (downloading packages)
3. Waiting - it should eventually complete

## Method 4: Check for Errors

If it's been stuck for more than 20 minutes, there might be an error. Try:

```bash
# Check if there's an error (this will show errors immediately)
nix develop --show-trace

# Or try with verbose output
nix develop --verbose
```

## Method 5: Use a Minimal Dev Shell

Create a minimal dev shell just for PureScript testing:

```bash
# Create a minimal shell.nix (temporary)
cat > shell.nix << 'EOF'
{ pkgs ? import <nixpkgs> {} }:
pkgs.mkShell {
  buildInputs = [
    pkgs.spago
    pkgs.purescript
    pkgs.nodejs_20
  ];
}
EOF

# Use the minimal shell
nix-shell
```

Then:
```bash
cd packages/console/app
spago -x test.dhall install
spago -x test.dhall test
```

## Recommended: Method 1 (Direct Nix Command)

This is the fastest way to run tests without waiting for the full dev shell:

```bash
cd /mnt/c/Users/justi/Desktop/CODER/packages/console/app
nix run nixpkgs#spago -- -x test.dhall install  # First time
nix run nixpkgs#spago -- -x test.dhall test
```
