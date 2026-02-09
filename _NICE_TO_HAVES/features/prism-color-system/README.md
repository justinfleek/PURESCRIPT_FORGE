# PRISM - Color System

Unified color theming system for terminals, editors, and IDEs.

## Components
- `PRISM/` - Theme definitions and generators
  - prism-color-core - Core color logic (Haskell/Lean4)
  - vscode-prism - VS Code theme
  - nvim-prism - Neovim theme
  - cursor-prism - Cursor theme
  - terminal-themes - Terminal themes

## Integration
1. Copy PRISM/ to project root
2. Add prism-color-core to flake.nix
3. Generate themes using build scripts
