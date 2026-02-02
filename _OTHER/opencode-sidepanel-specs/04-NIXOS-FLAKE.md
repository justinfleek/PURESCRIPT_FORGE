# 04-NIXOS-FLAKE: Reproducible Build Configuration

## Overview

The project uses Nix Flakes for reproducible builds and development environments. This ensures every developer and CI system has identical tooling.

**Why Nix?**
- Reproducibility across machines and time
- Target audience (senior engineers) respects the choice
- Eliminates "works on my machine" problems
- Single command to enter development environment

---

## Flake Structure

### flake.nix

```nix
{
  description = "OpenCode Sidepanel - Hybrid terminal-GUI experience";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    
    # PureScript tooling
    purescript-overlay = {
      url = "github:thomashoneyman/purescript-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    
    # Lean4
    lean4 = {
      url = "github:leanprover/lean4/v4.5.0";
    };
    
    # Node.js for bridge
    # (using nixpkgs nodejs)
  };

  outputs = { self, nixpkgs, flake-utils, purescript-overlay, lean4 }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ 
            purescript-overlay.overlays.default
          ];
        };
        
        # Lean4 packages for this system
        lean4Pkgs = lean4.packages.${system};
        
        # Node.js version
        nodejs = pkgs.nodejs_20;
        
        # Development tools
        devTools = with pkgs; [
          # Node.js
          nodejs
          nodePackages.pnpm
          nodePackages.typescript
          nodePackages.typescript-language-server
          
          # PureScript
          purescript
          spago-unstable
          purs-tidy
          purs-backend-es
          
          # Lean4
          lean4Pkgs.lean
          lean4Pkgs.lake
          
          # Build tools
          just
          watchexec
          jq
          
          # Testing
          nodePackages.playwright
          
          # Formatters & Linters
          nodePackages.prettier
          nodePackages.eslint
          
          # Git
          git
          gh
          
          # Misc
          ripgrep
          fd
        ];
        
        # Runtime dependencies
        runtimeDeps = with pkgs; [
          # For better-sqlite3
          sqlite
          
          # For native modules
          python3
          gnumake
          gcc
        ];
        
      in {
        # Development shell
        devShells.default = pkgs.mkShell {
          buildInputs = devTools ++ runtimeDeps;
          
          shellHook = ''
            echo "🚀 OpenCode Sidepanel Development Environment"
            echo ""
            echo "Available commands:"
            echo "  just dev     - Start development servers"
            echo "  just build   - Build all packages"
            echo "  just test    - Run all tests"
            echo "  just fmt     - Format all code"
            echo ""
            
            # Set up pnpm
            export PNPM_HOME="$HOME/.local/share/pnpm"
            export PATH="$PNPM_HOME:$PATH"
            
            # Set up npm global
            export NPM_CONFIG_PREFIX="$HOME/.npm-global"
            export PATH="$NPM_CONFIG_PREFIX/bin:$PATH"
            
            # Set up Lean
            export LEAN_PATH="${lean4Pkgs.lean}/lib/lean/library"
          '';
          
          # Environment variables
          LOCALE_ARCHIVE = "${pkgs.glibcLocales}/lib/locale/locale-archive";
          LC_ALL = "en_US.UTF-8";
        };
        
        # Packages
        packages = {
          # Bridge server
          bridge = pkgs.buildNpmPackage {
            pname = "opencode-sidepanel-bridge";
            version = "0.1.0";
            src = ./bridge;
            npmDepsHash = "sha256-AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA=";
            
            buildPhase = ''
              pnpm run build
            '';
            
            installPhase = ''
              mkdir -p $out/bin
              cp -r dist/* $out/
              
              # Create wrapper script
              cat > $out/bin/sidepanel-bridge << EOF
              #!/usr/bin/env bash
              exec ${nodejs}/bin/node $out/index.js "\$@"
              EOF
              chmod +x $out/bin/sidepanel-bridge
            '';
          };
          
          # Frontend bundle
          frontend = pkgs.stdenv.mkDerivation {
            pname = "opencode-sidepanel-frontend";
            version = "0.1.0";
            src = ./frontend;
            
            nativeBuildInputs = [ 
              pkgs.purescript
              pkgs.spago-unstable
              nodejs
              pkgs.nodePackages.pnpm
            ];
            
            buildPhase = ''
              export HOME=$TMPDIR
              spago bundle --to output/app.js
            '';
            
            installPhase = ''
              mkdir -p $out
              cp output/app.js $out/
              cp -r assets/* $out/
            '';
          };
          
          # Combined package
          default = pkgs.symlinkJoin {
            name = "opencode-sidepanel";
            paths = [
              self.packages.${system}.bridge
              self.packages.${system}.frontend
            ];
          };
        };
        
        # Checks (run in CI)
        checks = {
          # Format check
          format = pkgs.runCommand "format-check" {
            nativeBuildInputs = devTools;
          } ''
            cd ${self}
            purs-tidy check "frontend/src/**/*.purs" || exit 1
            prettier --check "bridge/src/**/*.ts" || exit 1
            touch $out
          '';
          
          # PureScript build check
          purescript = pkgs.runCommand "purescript-check" {
            nativeBuildInputs = devTools;
          } ''
            cd ${self}/frontend
            export HOME=$TMPDIR
            spago build
            touch $out
          '';
          
          # TypeScript build check
          typescript = pkgs.runCommand "typescript-check" {
            nativeBuildInputs = devTools;
          } ''
            cd ${self}/bridge
            export HOME=$TMPDIR
            pnpm install --frozen-lockfile
            pnpm run typecheck
            touch $out
          '';
        };
        
        # Apps (for nix run)
        apps = {
          default = flake-utils.lib.mkApp {
            drv = self.packages.${system}.bridge;
          };
          
          dev = flake-utils.lib.mkApp {
            drv = pkgs.writeShellScriptBin "dev" ''
              cd ${self}
              just dev
            '';
          };
        };
      }
    );
}
```

---

## Lock File Management

### Updating Dependencies

```bash
# Update all flake inputs
nix flake update

# Update specific input
nix flake lock --update-input nixpkgs

# Show current inputs
nix flake metadata
```

### flake.lock Structure

```json
{
  "nodes": {
    "nixpkgs": {
      "locked": {
        "lastModified": 1705000000,
        "narHash": "sha256-...",
        "owner": "NixOS",
        "repo": "nixpkgs",
        "rev": "...",
        "type": "github"
      }
    },
    "purescript-overlay": { ... },
    "lean4": { ... }
  }
}
```

---

## Development Shell

### Entering the Shell

```bash
# Enter development environment
nix develop

# Or with direnv (auto-enter)
echo "use flake" > .envrc
direnv allow
```

### Available Tools

After entering `nix develop`:

| Tool | Version | Purpose |
|------|---------|---------|
| `node` | 20.x | JavaScript runtime |
| `pnpm` | 8.x | Node package manager |
| `tsc` | 5.x | TypeScript compiler |
| `purs` | 0.15.x | PureScript compiler |
| `spago` | 0.21.x | PureScript build tool |
| `purs-tidy` | latest | PureScript formatter |
| `lean` | 4.5.x | Lean4 compiler |
| `lake` | latest | Lean4 build tool |
| `just` | latest | Command runner |
| `watchexec` | latest | File watcher |

### Shell Hook

The shell hook runs on entry:

```nix
shellHook = ''
  echo "🚀 OpenCode Sidepanel Development Environment"
  
  # Set up paths
  export PNPM_HOME="$HOME/.local/share/pnpm"
  export PATH="$PNPM_HOME:$PATH"
  
  # Install dependencies if needed
  if [ ! -d "node_modules" ]; then
    echo "Installing dependencies..."
    pnpm install
  fi
  
  if [ ! -d "frontend/.spago" ]; then
    echo "Installing PureScript packages..."
    cd frontend && spago install && cd ..
  fi
'';
```

---

## Building Packages

### Development Build

```bash
# Build everything
nix build

# Build specific package
nix build .#bridge
nix build .#frontend

# Build and run
nix run
```

### Production Build

```bash
# Build optimized bundle
nix build .#default

# Output structure
result/
├── bin/
│   └── sidepanel-bridge
├── app.js          # Frontend bundle
├── index.html
└── styles/
```

### Cross-Platform Builds

```bash
# Build for different systems
nix build .#packages.x86_64-linux.default
nix build .#packages.aarch64-darwin.default
```

---

## CI Integration

### GitHub Actions

```yaml
name: CI

on: [push, pull_request]

jobs:
  check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - uses: cachix/install-nix-action@v24
        with:
          extra_nix_config: |
            experimental-features = nix-command flakes
      
      - uses: cachix/cachix-action@v13
        with:
          name: opencode-sidepanel
          authToken: '${{ secrets.CACHIX_AUTH_TOKEN }}'
      
      - name: Check formatting
        run: nix flake check
      
      - name: Build
        run: nix build
      
      - name: Test
        run: nix develop --command just test
```

### Cachix Setup

```bash
# Create cache
cachix create opencode-sidepanel

# Push builds
nix build | cachix push opencode-sidepanel

# Configure in flake
{
  nixConfig = {
    extra-substituters = [
      "https://opencode-sidepanel.cachix.org"
    ];
    extra-trusted-public-keys = [
      "opencode-sidepanel.cachix.org-1:..."
    ];
  };
}
```

---

## Direnv Integration

### .envrc

```bash
# Use nix flake
use flake

# Extra environment variables
export VENICE_API_KEY_FILE="$HOME/.secrets/venice-api-key"

# Watch additional files
watch_file flake.nix
watch_file flake.lock
```

### .direnvrc

```bash
# Custom direnv functions
use_flake() {
  watch_file flake.nix
  watch_file flake.lock
  eval "$(nix print-dev-env --accept-flake-config)"
}
```

---

## Troubleshooting

### Common Issues

**Issue:** `purs: command not found`
```bash
# Make sure you're in the shell
nix develop
# Or check PATH
which purs
```

**Issue:** `spago install` fails
```bash
# Clear cache and retry
rm -rf .spago
spago install
```

**Issue:** Native modules fail to build
```bash
# Ensure build tools available
nix develop --command which gcc make python3
# Rebuild native modules
pnpm rebuild
```

**Issue:** Lean4 files not found
```bash
# Check LEAN_PATH
echo $LEAN_PATH
# Verify Lean installation
lean --version
```

### Debugging Nix

```bash
# Show derivation details
nix show-derivation .#bridge

# Build with verbose output
nix build -L .#bridge

# Enter build environment
nix develop .#bridge --command bash

# Check why something isn't building
nix why-depends .#default .#some-dependency
```

---

## Platform-Specific Notes

### macOS

```nix
# Darwin-specific settings
mkShell {
  buildInputs = devTools ++ (if pkgs.stdenv.isDarwin then [
    pkgs.darwin.apple_sdk.frameworks.Security
    pkgs.darwin.apple_sdk.frameworks.CoreFoundation
  ] else []);
}
```

### Linux

```nix
# Linux-specific settings
mkShell {
  buildInputs = devTools ++ (if pkgs.stdenv.isLinux then [
    pkgs.libsecret  # For keytar
  ] else []);
}
```

### WSL2

```bash
# Ensure systemd is enabled in /etc/wsl.conf
[boot]
systemd=true

# Then Nix daemon will work properly
```

---

## Related Specifications

- `05-DEVELOPMENT-SETUP.md` - First-time setup guide
- `08-DEVELOPMENT-WORKFLOW.md` - Day-to-day workflow
- `53-CICD-PIPELINE.md` - CI/CD configuration

---

*"Reproducibility is not a feature—it's a foundation."*
