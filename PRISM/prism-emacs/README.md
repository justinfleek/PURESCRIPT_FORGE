# Prism Themes for Emacs

**40 formally verified color themes** built with OKLCH color science.

## Installation

### MELPA (coming soon)

```elisp
(use-package prism-themes
  :ensure t
  :config
  (load-theme 'prism-fleek t))
```

### Manual Installation

1. Clone or download this repository
2. Add to your load path:

```elisp
(add-to-list 'load-path "/path/to/prism-emacs")
(add-to-list 'custom-theme-load-path "/path/to/prism-emacs/themes")
(require 'prism-themes)
(load-theme 'prism-fleek t)
```

### Straight.el

```elisp
(straight-use-package
 '(prism-themes :type git :host github :repo "fleek-ai/prism-emacs"))
(load-theme 'prism-fleek t)
```

### Doom Emacs

In `packages.el`:
```elisp
(package! prism-themes :recipe (:host github :repo "fleek-ai/prism-emacs"))
```

In `config.el`:
```elisp
(setq doom-theme 'prism-fleek)
```

## Usage

```elisp
;; Load a theme
(load-theme 'prism-fleek t)

;; Or use the interactive selector
M-x prism-themes-load
```

## Available Themes (40)

### 🏆 Flagship
- `prism-fleek` - Official Fleek brand theme
- `prism-fleek-light` - Light variant

### 💎 Luxury Collection
- `prism-nero-marquina` - Black marble with gold
- `prism-midnight-sapphire` - Deep blue gemstone
- `prism-obsidian-rose-gold` - Volcanic glass
- `prism-champagne-noir` - French elegance
- `prism-emerald-velvet` - Regal green
- `prism-diamond-dust` - White sophistication

### 🪟 Glass Collection
- `prism-aurora-glass` - Northern lights
- `prism-zen-garden` - Japanese minimalism
- `prism-tide-pool` - Aquatic depth
- `prism-porcelain-moon` - Lunar ceramic
- `prism-soft-charcoal` - Matte professional

### 🌈 Harmonious Collection
- `prism-ocean-depths` - Deep sea
- `prism-forest-canopy` - Dappled sunlight
- `prism-lavender-dusk` - Twilight purple
- `prism-slate-and-gold` - Luxury minimalism
- `prism-ember-hearth` - Warm fireplace
- `prism-constellation-map` - Night sky

### ⚡ Wild Collection
- `prism-neon-nexus` - Matrix green
- `prism-blood-moon` - Lunar eclipse
- `prism-vaporwave-sunset` - Retro 80s
- `prism-acid-rain` - Toxic industrial
- `prism-ultraviolet` - Blacklight
- `prism-holographic` - Iridescent
- `prism-cyber-noir` - Blade Runner
- `prism-synthwave-84` - Retro computing

### 📚 Classic Collection
- `prism-catppuccin-mocha`
- `prism-dracula-pro`
- `prism-gruvbox-material`
- `prism-moonlight-ii`
- `prism-nord-aurora`
- `prism-one-dark-pro`
- `prism-ayu-mirage`
- `prism-rose-pine`
- `prism-night-owl`
- `prism-cobalt2`
- `prism-palenight`
- `prism-vesper`
- `prism-tokyo-night-bento`

## Supported Packages

- Font Lock (built-in syntax)
- Org Mode
- Markdown Mode
- Company
- Magit
- Which-key
- Ivy/Counsel
- Flycheck
- LSP Mode
- Treemacs
- Rainbow Delimiters

## License

MIT License - Built by [Fleek AI](https://fleek.sh)
