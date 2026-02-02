# PRISM Theme Collection

**38 WCAG-Verified Color Themes × Multiple Platforms**

A curated collection of syntax themes with mathematically verified contrast ratios.

## Verified Color Science

PRISM uses **OKLCH perceptual color space** with **WCAG 2.1 contrast verification**:

- All text meets **WCAG AA** (4.5:1 contrast minimum)
- Comments meet **WCAG AA-Large** (3.0:1 minimum)
- Accents auto-adjust for accessibility
- Formal proofs in Lean4 (see `prism-color-core/lean4/`)

## Themes

### Core Straylight (12 themes)
**Ono-Sendai Dark:** Tuned, Memphis, Github
**Maas Biolabs Light:** Neoform, Biopic, Ghost, Tessier  
**Brand:** Fleek Gold, Fleek Gradient, Blood Moon, Minimal, Rose Gold

### Gradient Palettes (14 themes)
Coastal, Inferno, Faded Glory, Sunset, Forest, Ocean, Grape, Mint, Tropical, Arctic, Vesper, Vaporwave, Rose, Synthwave

### Community Favorites (12 themes)
Acid Rain, Catppuccin Mocha, Cobalt2, Dracula Pro, Gruvbox Material, Holographic, Night Owl, Nord Aurora, One Dark Pro, Rose Pine, Synthwave 84, Ultraviolet

## Platforms

- **VSCode / Cursor** - `cursor-prism/` or `prism-vscode-final/`
- **Neovim** - `nvim-prism/`
- **Emacs** - `prism-emacs/`
- **OpenCode** - `opencode-prism/`
- **Terminals** - `terminal-themes/` (Alacritty, Kitty, WezTerm, Windows Terminal)

## Installation

### VSCode / Cursor
1. Copy theme folder to `~/.vscode/extensions/` or `~/.cursor/extensions/`
2. Reload and select theme from Color Theme picker

### Neovim
```lua
-- Add to your config
require('prism').setup({ theme = 'tuned' })
```

### Emacs
```elisp
(add-to-list 'custom-theme-load-path "~/.emacs.d/themes/prism")
(load-theme 'prism-tuned t)
```

## License

MIT

## Creating Custom Themes

Use the theme generator:

```bash
cd prism-color-core/tools

# Option 1: Command line
python create_theme.py \
  --name "My Theme" \
  --bg "#1a1a1a" \
  --accent "#ff5500" \
  --fg "#ffffff" \
  --comment "#666666" \
  --hl "#252525" \
  --type dark

# Option 2: Edit CUSTOM_THEMES in create_theme.py and run:
python create_theme.py
```

Then copy the generated `.json` file to your editor's themes folder.

## Theme Generator (VSCode Extension)

The `vscode-prism/vscode-prism-theme-generator/` folder contains a full theme generator extension:

```bash
cd vscode-prism/vscode-prism-theme-generator
npm install
npm run compile
```

Then install in VSCode/Cursor. The generator:
1. Lets you pick a hue on a color wheel
2. Generates a full Base16 palette using OKLCH
3. **Verifies all colors meet WCAG contrast requirements**
4. Auto-adjusts colors that don't meet accessibility standards

The verification logic is in `src/prismColor.ts` - a TypeScript port of the formally verified Haskell implementation.
