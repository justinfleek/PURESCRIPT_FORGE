# Prism Terminal & Editor Themes

40 OKLCH color science themes for terminals, editors, and CLI tools.

## Supported Platforms

### Terminal Emulators
| Terminal | Format | Location | Installation |
|----------|--------|----------|--------------|
| **Alacritty** | TOML | `alacritty/` | `~/.config/alacritty/themes/` |
| **Kitty** | conf | `kitty/` | `include` in kitty.conf |
| **WezTerm** | TOML | `wezterm/` | `~/.config/wezterm/colors/` |
| **iTerm2** | itermcolors | `iterm2/` | Import via Preferences |
| **Windows Terminal** | JSON | `windows-terminal/` | Add to settings.json |

### Editors
| Editor | Format | Location | Installation |
|--------|--------|----------|--------------|
| **JetBrains** | ICLS | `jetbrains/` | File → Import Settings |
| **Zed** | JSON | `zed/` | `~/.config/zed/themes/` |
| **Helix** | TOML | `helix/` | `~/.config/helix/themes/` |

### CLI Tools
| Tool | Format | Location | Installation |
|------|--------|----------|--------------|
| **tmux** | conf | `tmux/` | `source` in .tmux.conf |
| **bat/delta** | JSON | `bat/` | `--theme` flag |
| **Starship** | TOML | `starship/` | Color palette reference |

## Quick Install

### Alacritty

```bash
# Copy theme to config
cp alacritty/fleek.toml ~/.config/alacritty/themes/

# Add to alacritty.toml
echo 'import = ["~/.config/alacritty/themes/fleek.toml"]' >> ~/.config/alacritty/alacritty.toml
```

### Kitty

```bash
# Copy theme
cp kitty/fleek.conf ~/.config/kitty/themes/

# Add to kitty.conf
echo 'include themes/fleek.conf' >> ~/.config/kitty/kitty.conf

# Or use kitty's built-in theme switcher
kitty +kitten themes --reload-in=all
```

### WezTerm

```bash
# Copy theme
mkdir -p ~/.config/wezterm/colors
cp wezterm/fleek.toml ~/.config/wezterm/colors/

# Add to wezterm.lua
cat >> ~/.config/wezterm/wezterm.lua << 'EOF'
local config = {}
config.color_scheme = 'Prism fleek'
return config
EOF
```

### iTerm2

1. Open iTerm2 → Preferences → Profiles → Colors
2. Click "Color Presets..." dropdown
3. Select "Import..."
4. Choose `iterm2/fleek.itermcolors`
5. Select the imported theme from the dropdown

## Theme Collections

### Flagship
- **fleek** - AI inference optimization aesthetic
- **fleek-light** - Light variant

### Luxury
Dark, sophisticated themes with metallic accents:
- nero-marquina, midnight-sapphire, obsidian-rose-gold
- champagne-noir, emerald-velvet, diamond-dust

### Glass
Translucent, ethereal aesthetics:
- aurora-glass, zen-garden, tide-pool
- porcelain-moon, soft-charcoal

### Harmonious
Natural, balanced palettes:
- ocean-depths, forest-canopy, lavender-dusk
- slate-and-gold, ember-hearth, constellation-map

### Wild
High energy, vibrant themes:
- neon-nexus, blood-moon, vaporwave-sunset
- acid-rain, ultraviolet, holographic
- cyber-noir, synthwave-84

### Classic
Refined versions of beloved themes:
- catppuccin-mocha, dracula-pro, gruvbox-material
- nord-aurora, one-dark-pro, ayu-mirage
- rose-pine, night-owl, cobalt2
- palenight, vesper, tokyo-night-bento, moonlight-ii

## Color Science

All themes use OKLCH color space for perceptual uniformity:
- Equal lightness steps appear equally bright
- Consistent chroma across hue angles
- Mathematically proven conversions (Lean4)

WCAG 2.1 AA contrast ratios verified:
- Normal text: ≥ 4.5:1
- Large text: ≥ 3.0:1

## Regenerating Themes

If you modify the source themes:

```bash
cd prism-color-core/tools
python generate_terminal_themes.py
```

## License

MIT License - See [LICENSE](../LICENSE)

---

*Part of the [Prism Theme System](https://github.com/weylai/prism-themes)*
