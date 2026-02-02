# PRISM CODE

## The AI Coding Agent That Makes You *Want* to Code

> "OpenCode, but for people who care about aesthetics as much as they care about shipping."

---

## Vision

Create the most visually stunning, buttery-smooth AI coding experience that makes even senior FAANG engineers feel like they're using something from the future. Not just a tool—an *experience*.

**Core Thesis:** The best developers in the world spend 8-14 hours a day looking at code. They deserve an environment that brings them joy, not just functionality.

---

## What Makes This Different

### OpenCode Is Good. We're Making It *Transcendent*.

| OpenCode | Prism Code |
|----------|------------|
| Functional themes | **Luxury material themes** (marble, glass, velvet) |
| Basic syntax colors | **OKLCH perceptually-uniform colors** with formally verified contrast |
| Static UI | **Micro-interactions** that respond to your coding rhythm |
| One-size-fits-all | **Adaptive UI** that learns your workflow |
| Terminal-only | **Desktop app with GPU-accelerated effects** |
| Standard keybinds | **Vim-native flow** with muscle-memory optimization |

---

## The Prism Experience

### 1. Luxury Themes That Feel Like Art

Not just colors. **Materials:**

```
nero_marquina     → Black Spanish marble with gold dust particles
obsidian_rose     → Volcanic glass with rose gold veins  
midnight_sapphire → Deep blue gemstone with platinum glow
aurora_glass      → Northern lights through frosted panels
tokyo_bento       → Japanese minimalism meets neon city
ember_hearth      → Warm fireplace, embers rise on keystrokes
constellation     → Star charts that connect as you code
```

Each theme has a **personality**:
- Visual effects (glow, particles, shimmer)
- Sound design (optional subtle audio feedback)
- Contextual behavior (ember_hearth gets "warmer" during flow state)

### 2. Micro-Interactions That Respond to You

**Cursor Spotlight**: Subtle radial glow follows your cursor (GPU-accelerated)

**Typing Pulse**: Editor breathes with your rhythm—fast typing = energy, slow = calm

**Flow State Detection**: After 5 minutes of uninterrupted coding:
- Colors subtly deepen
- Distractions fade
- Easter egg: Gold constellation lines connect your recent edits

**Milestone Celebrations**:
- Tests pass → Brief emerald flash
- Build succeeds → Satisfying gold shimmer
- PR merged → Champagne bubbles rise

**Idle Magic**: Leave for 30+ seconds and return to subtle ambient animation

### 3. The UI That FAANG Engineers Will Covet

**The Problem with Cursor/Claude Code**: They look like every other VS Code clone.

**Our Approach**:

```
┌─────────────────────────────────────────────────────────────────┐
│  PRISM CODE                                    ▣ □ ✕           │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │                                                          │  │
│  │                    CODE EDITOR                           │  │
│  │                                                          │  │
│  │    With real-time syntax highlighting                    │  │
│  │    and inline AI suggestions that                        │  │
│  │    *actually look good*                                  │  │
│  │                                                          │  │
│  └──────────────────────────────────────────────────────────┘  │
│                                                                 │
│  ┌─────────────────────┐  ┌─────────────────────────────────┐  │
│  │                     │  │                                 │  │
│  │   FILE TREE         │  │   AI CHAT                       │  │
│  │   Bento-style       │  │   Glassmorphism panels          │  │
│  │   floating cards    │  │   Smooth scroll                 │  │
│  │                     │  │   Code blocks with hover copy   │  │
│  │                     │  │                                 │  │
│  └─────────────────────┘  └─────────────────────────────────┘  │
│                                                                 │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │  λ ~/projects/myapp (main) $ _                           │  │
│  │                                         TERMINAL         │  │
│  └──────────────────────────────────────────────────────────┘  │
│                                                                 │
│  ◉ nero_marquina │ claude-4-opus │ 2.3k tokens │ flow: ████░░  │
└─────────────────────────────────────────────────────────────────┘
```

**Key UI Innovations**:

1. **Bento Layouts**: Floating cards with depth, not flat panels
2. **Glassmorphism AI Panel**: Frosted glass effect, content behind softly visible
3. **Neumorphic Controls**: Buttons that feel tactile
4. **Smooth Everything**: 60fps animations, spring physics, no jank
5. **Information Density**: More context visible, less scrolling
6. **Adaptive Layout**: Learns your preferred panel arrangement

### 4. The Terminal Experience (TUI)

Even in pure terminal, we elevate:

```
╭──────────────────────────────────────────────────────────────────╮
│  ✦ PRISM                                      nero_marquina     │
├──────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┃ You: Refactor the auth module to use JWT tokens              │
│                                                                  │
│  ┃ Prism: I'll refactor the authentication module. Let me       │
│  ┃ analyze the current implementation...                        │
│  ┃                                                              │
│  ┃ ╭─────────────────────────────────────────────────────────╮ │
│  ┃ │ auth/middleware.ts                        ◉ Modified    │ │
│  ┃ ├─────────────────────────────────────────────────────────┤ │
│  ┃ │  import jwt from 'jsonwebtoken';                        │ │
│  ┃ │                                                         │ │
│  ┃ │  export const verifyToken = async (token: string) => {  │ │
│  ┃ │    const decoded = jwt.verify(token, process.env.JWT);  │ │
│  ┃ │    return decoded as UserPayload;                       │ │
│  ┃ │  };                                                     │ │
│  ┃ ╰─────────────────────────────────────────────────────────╯ │
│                                                                  │
│  ┃ [y] Accept  [n] Reject  [e] Edit  [d] Diff  [?] Explain     │
│                                                                  │
╰──────────────────────────────────────────────────────────────────╯
  ▸ Type your message...                              ctrl+x for help
```

**TUI Enhancements**:
- Unicode box drawing that actually looks good
- True color gradients in borders
- Syntax highlighting with our OKLCH palette
- Smooth scrolling (via scroll_acceleration)
- Vim keybinds by default (toggleable)
- Status bar with flow state indicator

### 5. Desktop App: The Full Experience

Using Tauri (Rust) for native performance:

**GPU-Accelerated Effects**:
- Real-time cursor spotlight with WebGL
- Particle systems (gold dust, embers, aurora)
- Smooth 120fps animations on capable displays
- Background blur/glassmorphism

**Native Integration**:
- System theme detection (auto light/dark)
- Menu bar presence
- Notifications that match the aesthetic
- Drag-and-drop files directly into chat

**Multi-Window Support**:
- Detach AI chat to secondary monitor
- Floating terminal
- Picture-in-picture code preview

---

## Technical Architecture

### Fork Strategy

```
sst/opencode (upstream)
    │
    └── weyl-ai/prism-code (our fork)
            │
            ├── packages/prism-themes/      # Our theme system
            ├── packages/prism-effects/     # Micro-interactions
            ├── packages/prism-desktop/     # Tauri app
            └── packages/prism-tui/         # Enhanced TUI
```

### Theme Integration

OpenCode's theme system uses JSON with 62 color properties. We map our Base16 palettes:

```typescript
// prism-theme-adapter.ts
function prismToOpencode(preset: PrismPreset): OpenCodeTheme {
  const { palette, effects } = preset;
  return {
    // UI Colors
    background: palette.base00,
    backgroundSecondary: palette.base01,
    border: palette.base02,
    text: palette.base05,
    textMuted: palette.base04,
    accent: palette.base0A,  // HERO COLOR
    
    // Syntax (mapped to our formally-verified colors)
    syntaxComment: palette.base03,
    syntaxKeyword: palette.base0E,
    syntaxFunction: palette.base0D,
    syntaxString: palette.base0B,
    syntaxType: palette.base0A,  // Hero!
    syntaxNumber: palette.base09,
    
    // Diff
    diffAdded: palette.base0B,
    diffRemoved: palette.base08,
    diffModified: palette.base0D,
    
    // Effects metadata (custom extension)
    __prism: {
      glowColor: effects?.glowColor,
      glowIntensity: effects?.glowIntensity,
      particles: effects?.particles,
    }
  };
}
```

### Effect System Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                     PRISM EFFECT ENGINE                         │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────────┐ │
│  │   EVENTS    │  │   EFFECTS   │  │      RENDERERS          │ │
│  ├─────────────┤  ├─────────────┤  ├─────────────────────────┤ │
│  │ keystroke   │──│ typing_pulse│──│ TUI: ANSI color blend   │ │
│  │ cursor_move │──│ spotlight   │──│ Desktop: WebGL shader   │ │
│  │ file_save   │──│ milestone   │──│ Web: CSS animations     │ │
│  │ test_pass   │──│ celebration │──│                         │ │
│  │ idle        │──│ ambient     │──│                         │ │
│  │ flow_state  │──│ focus_mode  │──│                         │ │
│  └─────────────┘  └─────────────┘  └─────────────────────────┘ │
│                                                                 │
│  Performance Budget: <4ms per frame, respects reduced-motion   │
└─────────────────────────────────────────────────────────────────┘
```

---

## Feature Roadmap

### Phase 1: Theme Integration (Week 1-2)
- [ ] Fork OpenCode
- [ ] Create Prism theme JSON files for all 14 luxury presets
- [ ] Test in TUI
- [ ] Add theme selection UI enhancement
- [ ] Submit upstream PR for theme improvements

### Phase 2: TUI Enhancements (Week 3-4)
- [ ] Enhanced box drawing characters
- [ ] Smooth scrolling improvements
- [ ] Vim keybinds configuration
- [ ] Status bar with flow state
- [ ] Better syntax highlighting

### Phase 3: Desktop App (Week 5-8)
- [ ] Tauri shell with OpenCode backend
- [ ] GPU-accelerated cursor spotlight
- [ ] Glassmorphism panels
- [ ] Particle effects system
- [ ] Native notifications

### Phase 4: Advanced Features (Week 9-12)
- [ ] Flow state detection algorithm
- [ ] Adaptive UI layouts
- [ ] Sound design (optional)
- [ ] Easter eggs and achievements
- [ ] Community theme marketplace

---

## Why This Wins

### The Cursor/Claude Code Problem

1. **They look corporate** - Built for enterprise demos, not developer joy
2. **No personality** - One theme fits all = no one feels at home
3. **Missed opportunity** - AI is magical, the UI should feel magical too

### Our Advantage

1. **We understand developers** - Built by devs who care about their environment
2. **Formally-verified color science** - Not just "looks nice", provably optimal contrast
3. **Open source** - Community can contribute themes and effects
4. **Multi-platform** - TUI, desktop, and web—all beautiful

### The Emotional Hook

When a developer opens Prism Code for the first time, we want them to think:

> "Holy shit. This is what coding should feel like."

Not impressed by features. Impressed by *feel*.

---

## Name Options

1. **Prism Code** - Plays on light refraction, color science heritage
2. **Lumen** - Light-focused, clean
3. **Aureate** - Golden, premium feeling
4. **Obsidian Code** - Dark, premium (but Obsidian.md exists)
5. **Weyl Code** - Your company name, mathematical heritage

---

## Next Steps

1. **Fork OpenCode** → github.com/weyl-ai/prism-code
2. **Integrate Prism themes** → Convert our presets to OpenCode JSON
3. **Set up CI/CD** → Automated builds for TUI, desktop, web
4. **Create landing page** → prism-code.dev with live theme preview
5. **Alpha release** → Get it in the hands of 10 devs who care about aesthetics

---

## Resources

- OpenCode repo: https://github.com/sst/opencode
- OpenTUI framework: https://github.com/sst/opentui
- Prism themes: /home/claude/prism-color-core/themes/
- Effect engine: /home/claude/prism-color-core/effects/

---

*"The details are not the details. They make the design."* — Charles Eames
