# Prism Premium Themes - Plugin Integration

Luxury color themes with OKLCH perceptual uniformity, micro-interactions, and formally verified color science.

## Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│                      PRISM COLOR CORE                           │
│  - Haskell backend with OKLCH color science                     │
│  - Lean4 proofs for perceptual uniformity                       │
│  - Base16 palette generation                                    │
│  - luxury-presets.json with effects metadata                    │
└────────────────────────────┬────────────────────────────────────┘
                             │
        ┌────────────────────┼────────────────────┐
        ▼                    ▼                    ▼
┌───────────────┐    ┌───────────────┐    ┌───────────────┐
│    VSCode     │    │    Neovim     │    │    Emacs      │
│   Extension   │    │    Plugin     │    │   Package     │
├───────────────┤    ├───────────────┤    ├───────────────┤
│ • Webview UI  │    │ • Lua config  │    │ • Elisp       │
│ • Full CSS/JS │    │ • Telescope   │    │ • Faces       │
│   effects     │    │   picker      │    │ • Mode-line   │
│ • Theme JSON  │    │ • Terminal    │    │ • Terminal &  │
│   generation  │    │   colors      │    │   GUI support │
└───────────────┘    └───────────────┘    └───────────────┘
```

## VSCode Integration

### Installation

1. Copy the extension to your VS Code extensions folder:
```bash
cp -r vscode-prism-theme-generator ~/.vscode/extensions/
```

2. Reload VS Code

### Commands

| Command | Description |
|---------|-------------|
| `Prism Theme: Open Premium Theme Gallery` | Browse themes with visual preview |
| `Prism Theme: Apply Theme Preset` | Quick-pick any preset |
| `Prism Theme: Browse Themes by Category` | Filter by category first |
| `Prism Theme: Generate All Theme Files` | Pre-generate all theme JSONs |

### Key Files

- `src/presetGallery.ts` - All 14 luxury preset definitions
- `src/themeInstaller.ts` - Converts Base16 to VS Code theme JSON
- `src/themeGeneratorPanelV2.ts` - Premium gallery webview UI
- `src/extension.ts` - Command registrations

### Micro-Interactions (Webview Only)

The webview UI includes:
- **Cursor spotlight** - Subtle gold glow follows cursor
- **Hover effects** - Cards lift on hover
- **Gold shimmer** - Subtle animation on preview cards

These effects are CSS-only and don't affect the actual editor.

---

## Neovim Integration

### Installation

Using lazy.nvim:
```lua
{
  "weyl-ai/nvim-prism",
  lazy = false,
  priority = 1000,
  config = function()
    require("prism").setup({
      preset = "nero_marquina",  -- Default theme
      terminal_colors = true,
      transparent = false,
      effects = {
        cursor_glow = true,
        statusline_accent = true,
      },
    })
  end,
}
```

Using packer:
```lua
use {
  "weyl-ai/nvim-prism",
  config = function()
    require("prism").setup({ preset = "nero_marquina" })
  end
}
```

### Commands

| Command | Description |
|---------|-------------|
| `:Prism <preset>` | Apply a preset (tab-complete available) |
| `:PrismGallery` | Open Telescope picker with live preview |

### Available Presets

**Luxury Marble:**
- `nero_marquina` - Black Spanish marble + gold
- `obsidian_rose_gold` - Volcanic glass + rose gold
- `midnight_sapphire` - Deep blue + platinum
- `emerald_velvet` - Emerald on black velvet
- `champagne_noir` - Matte black + champagne gold

**Glassmorphism:**
- `aurora_glass` - Northern lights through ice
- `diamond_dust` - Ice crystals + sparkle

**Bento:**
- `tokyo_night_bento` - Japanese minimalism + neon
- `zen_garden` - Sand, moss, and stone

**Neumorphism:**
- `soft_charcoal` - Warm charcoal clay
- `porcelain_moon` - Light mode, bone china

**Responsive:**
- `ember_hearth` - Warm fireplace embers
- `tide_pool` - Bioluminescent ocean

**Easter Eggs:**
- `constellation_map` - Star charts with gold

### Terminal Effects (Limited)

Neovim supports limited effects in terminal:
- **Cursor glow** - Subtle blend on cursor line
- **Save flash** - Brief hero color flash on save
- **Idle breathing** - Subtle float window animation after 30s idle

### Key Files

- `lua/prism/init.lua` - Main entry point
- `lua/prism/presets.lua` - All preset definitions
- `lua/prism/highlights.lua` - Neovim highlight groups
- `lua/prism/terminal.lua` - Terminal ANSI colors
- `lua/prism/effects.lua` - Terminal-safe effects
- `lua/prism/telescope.lua` - Telescope integration

---

## Emacs Integration (Planned)

```elisp
;; Installation
(use-package prism-theme
  :config
  (prism-load-preset 'nero-marquina))

;; Commands
M-x prism-select-preset    ; Completing-read picker
M-x prism-browse-category  ; Filter by category
```

---

## Theme Color Mapping

All themes use the Base16 color scheme:

| Base | Role | Typical Use |
|------|------|-------------|
| base00 | Background | Editor background |
| base01 | Surface | Lighter background (panels) |
| base02 | Selection | Visual selection |
| base03 | Comments | Comments, line numbers |
| base04 | Dark foreground | Secondary text |
| base05 | Foreground | Main text |
| base06 | Light foreground | Brighter text |
| base07 | Bright | Brightest text |
| base08 | Red | Errors, tags |
| base09 | Orange | Numbers, constants |
| base0A | **Yellow (HERO)** | Types, hero color |
| base0B | Green | Strings |
| base0C | Cyan | Special, regex |
| base0D | Blue | Functions |
| base0E | Purple | Keywords |
| base0F | Brown | Deprecated |

The **Hero Color** (base0A) is the accent that defines each theme's personality.

---

## Effect Capabilities

| Effect | VSCode | Neovim Term | Neovim GUI | Emacs TTY | Emacs GUI |
|--------|--------|-------------|------------|-----------|-----------|
| Cursor spotlight | ✅ | ❌ | ❌ | ❌ | ⚠️ |
| Ambient particles | ✅ | ❌ | ❌ | ❌ | ❌ |
| Hover lift | ✅ | ⚠️ | ⚠️ | ❌ | ⚠️ |
| Glass blur | ✅ | ⚠️ | ⚠️ | ❌ | ⚠️ |
| Glow effects | ✅ | ⚠️ | ⚠️ | ❌ | ⚠️ |
| True colors | ✅ | ✅ | ✅ | ⚠️ | ✅ |
| Easter eggs | ✅ | ⚠️ | ⚠️ | ⚠️ | ⚠️ |

✅ Full support | ⚠️ Partial/approximated | ❌ Not possible

---

## Building from Source

### VSCode Extension

```bash
cd vscode-prism-theme-generator
npm install
npm run compile
npm run package  # Creates .vsix
```

### Haskell Backend (Optional)

The Haskell backend provides formally verified color generation:

```bash
cd prism-color-core/haskell
cabal build
cabal install --installdir=./bin
```

Without the backend, presets use pre-computed palettes.

---

## File Structure

```
prism-color-core/
├── haskell/                    # Formal verification backend
├── themes/
│   ├── luxury-presets.json     # Full preset definitions
│   ├── presets.json            # Original presets
│   └── premium-gallery.html    # Visual preview
├── effects/
│   └── micro-interactions.ts   # Effect engine
└── docs/
    └── PLUGIN_INTEGRATION.md   # This file

vscode-prism-theme-generator/
├── src/
│   ├── extension.ts            # Entry point
│   ├── presetGallery.ts        # Preset definitions
│   ├── themeInstaller.ts       # VS Code theme generator
│   └── themeGeneratorPanelV2.ts# Gallery UI
└── package.json

nvim-prism/
├── lua/prism/
│   ├── init.lua               # Entry point
│   ├── presets.lua            # Preset definitions
│   ├── highlights.lua         # Highlight groups
│   ├── terminal.lua           # Terminal colors
│   ├── effects.lua            # Terminal effects
│   └── telescope.lua          # Telescope picker
└── colors/                    # Generated colorschemes
```

---

## Credits

- **OKLCH Color Science**: Perceptually uniform color space
- **Base16**: Consistent color mapping across editors
- **Lean4**: Formal proofs of color properties
- **Inspiration**: ComfyUI Niutonian Themes, Enhanced Links & Nodes

## License

MIT
