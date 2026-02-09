# Prism Themes for OpenCode

**40 OKLCH Color Science Themes** for [OpenCode](https://opencode.ai) - the AI coding assistant for your terminal.

Every theme is mathematically designed using perceptually uniform OKLCH color space with formally verified contrast ratios.

![Prism Themes](https://img.shields.io/badge/themes-40-brightgreen)
![OKLCH](https://img.shields.io/badge/color%20space-OKLCH-blue)
![WCAG AA](https://img.shields.io/badge/contrast-WCAG%20AA-green)

## Installation

### Quick Install (Recommended)

```bash
# Clone to OpenCode themes directory
mkdir -p ~/.config/opencode/themes
cp themes/*.json ~/.config/opencode/themes/

# Or download specific theme
curl -o ~/.config/opencode/themes/fleek.json \
  https://raw.githubusercontent.com/weylai/prism-themes/main/opencode/themes/fleek.json
```

### Manual Installation

1. Download the theme JSON file you want
2. Place it in `~/.config/opencode/themes/`
3. In OpenCode, run `/theme` and select your theme

### Per-Project Configuration

Add to your project's `opencode.json` or `.opencode.json`:

```json
{
  "tui": {
    "theme": "fleek"
  }
}
```

## Theme Gallery

### Flagship Themes
| Theme | Description |
|-------|-------------|
| **fleek** | Official Fleek theme - AI inference meets polyhedral elegance |
| **fleek-light** | Light variant of the Fleek theme |

### Luxury Collection
| Theme | Description |
|-------|-------------|
| **nero-marquina** | Italian black marble with subtle gold veining |
| **midnight-sapphire** | Deep blue with silver accents |
| **obsidian-rose-gold** | Volcanic black with warm metallic highlights |
| **champagne-noir** | Sophisticated dark champagne palette |
| **emerald-velvet** | Rich emerald with cream accents |
| **diamond-dust** | Crystalline clarity with prismatic highlights |

### Glass Collection
| Theme | Description |
|-------|-------------|
| **aurora-glass** | Northern lights through frosted glass |
| **zen-garden** | Tranquil stone and moss tones |
| **tide-pool** | Coastal aquamarine and sand |
| **porcelain-moon** | Delicate lunar whites and grays |
| **soft-charcoal** | Warm neutral charcoal |

### Harmonious Collection
| Theme | Description |
|-------|-------------|
| **ocean-depths** | Deep sea blues and aquamarine |
| **forest-canopy** | Woodland greens and earth tones |
| **lavender-dusk** | Soft purples and sunset pinks |
| **slate-and-gold** | Professional slate with gold accents |
| **ember-hearth** | Warm fire and ember tones |
| **constellation-map** | Night sky navigation charts |

### Wild Collection
| Theme | Description |
|-------|-------------|
| **neon-nexus** | Cyberpunk neon brilliance |
| **blood-moon** | Deep crimson eclipse |
| **vaporwave-sunset** | Retro synthwave gradients |
| **acid-rain** | Toxic greens and industrial grays |
| **ultraviolet** | Deep purple UV glow |
| **holographic** | Iridescent rainbow shimmer |
| **cyber-noir** | Dark cyberpunk with cyan accents |
| **synthwave-84** | Retro '80s synthwave |

### Classic Reimagined
| Theme | Description |
|-------|-------------|
| **catppuccin-mocha** | Catppuccin Mocha with OKLCH precision |
| **dracula-pro** | Enhanced Dracula palette |
| **gruvbox-material** | Warm retro Gruvbox |
| **moonlight-ii** | Moonlight theme refined |
| **nord-aurora** | Nordic colors with aurora |
| **one-dark-pro** | Atom One Dark enhanced |
| **ayu-mirage** | Ayu Mirage refined |
| **rose-pine** | Rosé Pine with perfect contrast |
| **night-owl** | Sarah Drasner's Night Owl |
| **cobalt2** | Wes Bos's Cobalt2 refined |
| **palenight** | Material Palenight |
| **vesper** | Calm minimal dark |
| **tokyo-night-bento** | Tokyo Night with bento aesthetics |

## Color Science

All Prism themes are built on:

- **OKLCH Color Space**: Perceptually uniform lightness, chroma, and hue
- **WCAG 2.1 AA Compliance**: ≥4.5:1 contrast for normal text
- **OLED Black Balance**: Minimum L=0.11 (~#1a1a1a) to prevent smearing
- **Harmonious Palettes**: Mathematical color relationships for visual coherence

### Formally Verified

Color calculations are verified in Lean4 with Mathlib4:
- sRGB ↔ Linear RGB ↔ XYZ ↔ OKLAB ↔ OKLCH conversions
- WCAG contrast ratio calculations
- Bounds proofs for all color transformations

## Contributing

1. Fork the repository
2. Create your theme in the source format
3. Ensure WCAG AA compliance
4. Submit a pull request

## License

MIT License - see [LICENSE](LICENSE)

## Credits

Created by [Weyl AI](https://fleek.sh) for the developer community.

Part of the **Prism Theme System** - also available for:
- [VS Code / Cursor](../vscode)
- [Neovim](../nvim)
- [Emacs](../emacs)
