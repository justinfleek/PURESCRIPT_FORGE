# Nix Setup: Fixing Git Tracking Issue

## Problem
Nix flakes require files to be tracked by Git. The flake.nix file isn't tracked.

## Solution 1: Use --impure Flag (Quickest)

```bash
# From WSL, in CODER directory
nix develop --impure
```

This bypasses the Git requirement and works immediately.

---

## Solution 2: Add flake.nix to Git (Recommended)

```bash
# From WSL, in CODER directory
git add flake.nix flake.lock

# Then try again
nix develop
```

---

## Solution 3: Initialize Git Repo in CODER (Cleanest)

```bash
# From WSL, in CODER directory
git init
git add flake.nix flake.lock
git commit -m "Initial commit: Nix flake"

# Then
nix develop
```

---

## Recommended: Use --impure for Now

For development, `--impure` is fine. You can add files to Git later.

```bash
nix develop --impure
```

---

## Verify It Works

Once in the Nix shell:
```bash
which purs
which spago
which lean
nix flake show
```

---

**Last Updated:** 2026-01-30
