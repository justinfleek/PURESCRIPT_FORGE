# ✦ PRISM CODE

<div align="center">

**The AI coding agent that makes you *want* to code.**

[![Discord](https://img.shields.io/badge/Discord-Join-7289da?style=flat-square)](https://discord.gg/prismcode)
[![License](https://img.shields.io/badge/License-MIT-gold?style=flat-square)](LICENSE)
[![Stars](https://img.shields.io/github/stars/weyl-ai/prism-code?style=flat-square&color=gold)](https://github.com/weyl-ai/prism-code)

*A fork of [OpenCode](https://opencode.ai) with luxury themes, micro-interactions, and an obsessive attention to visual detail.*

</div>

---

## Why Prism Code?

You spend 8-14 hours a day looking at code. You deserve an environment that brings you **joy**, not just functionality.

Cursor and Claude Code are *fine*. They look corporate. Built for enterprise demos.

**Prism Code is different.** It's built for developers who care about aesthetics as much as they care about shipping.

---

## ✨ Features

### Luxury Themes

Not just colors. **Materials.**

| Theme | Inspiration |
|-------|-------------|
| **Nero Marquina** | Black Spanish marble with gold dust particles |
| **Obsidian Rose Gold** | Volcanic glass with rose gold veins |
| **Midnight Sapphire** | Deep blue gemstone with platinum glow |
| **Aurora Glass** | Northern lights through frosted panels |
| **Tokyo Night Bento** | Japanese minimalism meets neon cityscape |
| **Ember Hearth** | Warm fireplace, embers rise on keystrokes |
| **Constellation Map** | Star charts that connect as you code |

All themes use **OKLCH perceptually-uniform colors** with formally-verified contrast ratios.

### Micro-Interactions

- **Cursor Spotlight**: Subtle radial glow follows your cursor
- **Typing Pulse**: Editor breathes with your rhythm
- **Flow State Detection**: Colors deepen during focused coding
- **Milestone Celebrations**: Satisfying feedback when tests pass

### Everything OpenCode Has

- 100% open source
- Any AI provider (Claude, GPT, Gemini, local)
- LSP integration out of the box
- Session management
- Tool execution with approval
- GitHub integration

---

## 📦 Installation

```bash
# Quick install
curl -fsSL https://prism-code.dev/install | bash

# Or via npm
npm i -g prism-code

# Or via Homebrew
brew install weyl-ai/tap/prism-code
```

---

## 🎨 Theme Gallery

### Nero Marquina
Black Spanish marble with warm gold leaf accents.

```
Background: #08080a (OLED-optimized pure black)
Hero Color: #d4af37 (24K gold)
Effect: Gold dust particles, subtle vein shimmer
```

### Tokyo Night Bento
Japanese minimalism meets neon-lit cityscape.

```
Background: #0f0f18
Hero Color: #bb9af7 (Soft purple neon)
Effect: Gradient accent lines, bento card layouts
```

### Ember Hearth
Warm fireplace with embers responding to activity.

```
Background: #0c0908 (Warm charcoal)
Hero Color: #ffd93d (Firelight gold)
Effect: Rising ember particles on keystrokes
```

[View all themes →](https://prism-code.dev/themes)

---

## ⚙️ Configuration

```json
// ~/.config/prism-code/config.json
{
  "theme": "nero-marquina",
  "effects": {
    "cursorSpotlight": true,
    "typingPulse": true,
    "flowState": true,
    "milestones": true
  },
  "providers": {
    "default": "anthropic"
  }
}
```

---

## 🛠️ Development

```bash
# Clone the repo
git clone https://github.com/weyl-ai/prism-code
cd prism-code

# Install dependencies
bun install

# Generate themes
bun run generate-themes

# Start development
bun run dev
```

---

## 🤝 Contributing

We love contributions! See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

**Theme contributions especially welcome.** If you design a beautiful theme, we want it.

---

## 📜 License

MIT License - fork it, modify it, ship it.

Based on [OpenCode](https://github.com/sst/opencode) by SST.

---

<div align="center">

**"The details are not the details. They make the design."**

*— Charles Eames*

</div>
