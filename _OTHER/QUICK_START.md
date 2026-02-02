# Quick Start: Entering Nix Development Environment

## From PowerShell to Nix Flake

### Step 1: Enter WSL/Ubuntu
```powershell
wsl
```

### Step 2: Navigate to CODER Directory
```bash
cd /mnt/c/Users/justi/Desktop/CODER
```

### Step 3: Enter Nix Development Shell
```bash
nix develop
```

### Step 4: Verify You're In
```bash
# Should show Nix tools available
which purs
which spago
which lean
```

---

## One-Liner (From PowerShell)
```powershell
wsl bash -c "cd /mnt/c/Users/justi/Desktop/CODER && nix develop"
```

---

## Alternative: Direct Nix Commands (From PowerShell via WSL)
```powershell
wsl nix develop /mnt/c/Users/justi/Desktop/CODER
```

---

## If Nix Not Installed in WSL

### Install Nix in WSL:
```bash
sh <(curl -L https://nixos.org/nix/install) --daemon
```

### Then enable flakes:
```bash
mkdir -p ~/.config/nix
echo "experimental-features = nix-command flakes" >> ~/.config/nix/nix.conf
```

---

## Verify Flake Works
```bash
# From WSL, in CODER directory
nix flake show
```

---

## Build a Package
```bash
# Build Bridge Server
nix build .#bridge-server-ps

# Build Sidepanel
nix build .#sidepanel-ps

# Build everything
nix build
```

---

## Common Issues

### Issue: "command not found: nix"
**Solution:** Nix not installed in WSL. Install it (see above).

### Issue: "experimental-features" error
**Solution:** Enable flakes in `~/.config/nix/nix.conf`

### Issue: "path does not exist"
**Solution:** Make sure you're in the right directory:
```bash
pwd  # Should show /mnt/c/Users/justi/Desktop/CODER
ls flake.nix  # Should show the file
```

---

## Recommended Workflow

1. **Open PowerShell**
2. **Enter WSL:** `wsl`
3. **Navigate:** `cd /mnt/c/Users/justi/Desktop/CODER`
4. **Enter dev shell:** `nix develop`
5. **Work in Nix environment**
6. **Exit when done:** `exit` (exits Nix shell, then `exit` again exits WSL)

---

**Last Updated:** 2026-01-30
