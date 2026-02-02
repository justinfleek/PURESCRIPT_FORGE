# 90-FLEEK-BRAND-INTEGRATION: Design System and Visual Identity

## Overview

The OpenCode Sidepanel uses the Fleek brand identity, featuring the lightning bolt logo, rainbow gradient accents, circuit patterns, and the Fraunces typeface.

---

## Brand Colors

### Primary Palette (Rainbow Gradient)

```css
:root {
  /* Fleek Rainbow - Primary accent colors */
  --fleek-blue: #0090ff;
  --fleek-green: #32e48e;
  --fleek-yellow: #ffe629;
  --fleek-orange: #f76b15;
  
  /* Gradient stops for rainbow bar */
  --rainbow-gradient: linear-gradient(
    90deg,
    #0090ff 0%,
    #32e48e 33%,
    #ffe629 66%,
    #f76b15 100%
  );
}
```

### Neutral Palette (Dark Theme Base)

```css
:root {
  /* Background layers */
  --bg-base: #0a0a0a;
  --bg-surface: #111111;
  --bg-elevated: #1a1a1a;
  --bg-overlay: #222222;
  
  /* Text hierarchy */
  --text-primary: #ffffff;
  --text-secondary: #a0a0a0;
  --text-tertiary: #666666;
  --text-disabled: #444444;
  
  /* Borders */
  --border-subtle: #222222;
  --border-default: #333333;
  --border-strong: #444444;
}
```

### Semantic Colors

```css
:root {
  /* Status indicators */
  --status-success: #32e48e;    /* Fleek green */
  --status-warning: #ffe629;    /* Fleek yellow */
  --status-error: #ff4444;
  --status-info: #0090ff;       /* Fleek blue */
  
  /* Diem-specific states */
  --diem-healthy: #32e48e;      /* >50% balance */
  --diem-caution: #ffe629;      /* 25-50% balance */
  --diem-warning: #f76b15;      /* 10-25% balance */
  --diem-critical: #ff4444;     /* <10% balance */
}
```

---

## Typography

### Typefaces

```css
@font-face {
  font-family: 'Fraunces';
  src: url('/fonts/Fraunces-Medium.ttf') format('truetype');
  font-weight: 500;
  font-style: normal;
  font-display: swap;
}

@font-face {
  font-family: 'Fraunces';
  src: url('/fonts/Fraunces-SemiBold.ttf') format('truetype');
  font-weight: 600;
  font-style: normal;
  font-display: swap;
}

:root {
  /* Font stacks */
  --font-display: 'Fraunces', Georgia, 'Times New Roman', serif;
  --font-body: 'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
  --font-mono: 'JetBrains Mono', 'Fira Code', 'SF Mono', Consolas, monospace;
}
```

### Type Scale

```css
:root {
  /* Display - Fraunces for headlines */
  --text-display: 600 2.5rem/1.1 var(--font-display);
  --text-h1: 600 2rem/1.2 var(--font-display);
  --text-h2: 600 1.5rem/1.25 var(--font-display);
  --text-h3: 500 1.25rem/1.3 var(--font-display);
  
  /* Body - Inter for readability */
  --text-body: 400 1rem/1.5 var(--font-body);
  --text-body-sm: 400 0.875rem/1.5 var(--font-body);
  --text-caption: 400 0.75rem/1.4 var(--font-body);
  
  /* Code - Monospace */
  --text-code: 400 0.875rem/1.5 var(--font-mono);
  --text-code-sm: 400 0.75rem/1.4 var(--font-mono);
}
```

---

## Logo Usage

### Lightning Bolt Icon

```svg
<!-- Fleek Lightning Bolt - For favicon, app icon -->
<svg viewBox="0 0 14 38" fill="none" xmlns="http://www.w3.org/2000/svg">
  <path d="M12.35 13.24c.54 0 .87.63.59 1.11l-3.53 6.05h2.77c.58 0 .9.7.55 1.18L1.25 37.3c-.49.67-1.5.08-1.21-.71l4.56-12.27H1.67c-.54 0-.88-.63-.59-1.11l3.53-6.05H1.84c-.58 0-.9-.7-.55-1.18L12.77.29c.49-.67 1.49-.08 1.2.71L9.41 13.24h2.94z" fill="currentColor"/>
</svg>
```

### Logo Placement Rules

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  HEADER BAR                                                                 │
├─────────────────────────────────────────────────────────────────────────────┤
│  ⚡ fleek                                     [Rainbow gradient bar 4px]    │
├═══════════════════════════════════════════════════════════════════════════━┤
│                                                                             │
│  Logo appears in header with 16px lightning bolt + "fleek" wordmark         │
│  Rainbow gradient bar runs full width below header (4px height)             │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Decorative Elements

### Rainbow Gradient Bar

```html
<!-- Use as accent separator -->
<div class="fleek-rainbow-bar"></div>

<style>
.fleek-rainbow-bar {
  height: 4px;
  background: var(--rainbow-gradient);
  width: 100%;
}

/* Animated version for loading states */
.fleek-rainbow-bar--animated {
  background-size: 200% 100%;
  animation: rainbow-shift 2s linear infinite;
}

@keyframes rainbow-shift {
  0% { background-position: 0% 50%; }
  100% { background-position: 200% 50%; }
}
</style>
```

### Circuit Pattern Background

```html
<!-- Use as subtle background texture -->
<div class="fleek-circuit-bg"></div>

<style>
.fleek-circuit-bg {
  background-image: url('/images/brand/circuit-pattern-minimal.svg');
  background-repeat: repeat;
  background-size: 200px;
  opacity: 0.03;
  position: absolute;
  inset: 0;
  pointer-events: none;
}
</style>
```

### Grain Texture Overlay

```html
<!-- Subtle noise texture for depth -->
<div class="fleek-grain"></div>

<style>
.fleek-grain {
  background-image: url('/images/brand/fleek-grain-tile.svg');
  background-repeat: repeat;
  opacity: 0.02;
  mix-blend-mode: overlay;
  position: absolute;
  inset: 0;
  pointer-events: none;
}
</style>
```

---

## Component Styling

### Diem Balance Widget (Fleek Branded)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │  DIEM BALANCE                                      ⚡ fleek         │   │
│  ├─────────────────────────────────────────────────────────────────────┤   │
│  │                                                                     │   │
│  │      ████████████████░░░░░░░░░░░░░░░░░░░░░░░░░░░░░░               │   │
│  │      [Rainbow gradient progress bar]                               │   │
│  │                                                                     │   │
│  │                     42.5                                           │   │
│  │                     ────                                           │   │
│  │                    DIEM                                            │   │
│  │                                                                     │   │
│  │      -5.2/hr             Resets in 4:23:15                        │   │
│  │      burn rate           UTC midnight                              │   │
│  │                                                                     │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────────────────────┘
```

```css
.diem-widget {
  background: var(--bg-surface);
  border: 1px solid var(--border-subtle);
  border-radius: 12px;
  padding: 20px;
  position: relative;
  overflow: hidden;
}

.diem-widget::before {
  content: '';
  position: absolute;
  inset: 0;
  background-image: url('/images/brand/circuit-pattern-minimal.svg');
  opacity: 0.02;
}

.diem-progress {
  height: 8px;
  border-radius: 4px;
  background: var(--bg-overlay);
  overflow: hidden;
}

.diem-progress__fill {
  height: 100%;
  background: var(--rainbow-gradient);
  transition: width 0.3s ease;
}

.diem-value {
  font: var(--text-display);
  color: var(--text-primary);
  text-align: center;
  margin: 24px 0 8px;
}

.diem-label {
  font: var(--text-caption);
  color: var(--text-secondary);
  text-transform: uppercase;
  letter-spacing: 0.1em;
  text-align: center;
}
```

### Session Tab (Fleek Branded)

```css
.session-tab {
  background: var(--bg-surface);
  border: 1px solid var(--border-subtle);
  border-radius: 8px;
  padding: 12px 16px;
  cursor: pointer;
  transition: all 0.15s ease;
}

.session-tab:hover {
  background: var(--bg-elevated);
  border-color: var(--border-default);
}

.session-tab--active {
  background: var(--bg-elevated);
  border-color: var(--fleek-blue);
  box-shadow: 0 0 0 1px var(--fleek-blue);
}

/* Rainbow underline on active */
.session-tab--active::after {
  content: '';
  position: absolute;
  bottom: 0;
  left: 0;
  right: 0;
  height: 2px;
  background: var(--rainbow-gradient);
}
```

### Button Styles

```css
/* Primary - Rainbow gradient background */
.btn-primary {
  background: var(--rainbow-gradient);
  color: var(--bg-base);
  font: var(--text-body);
  font-weight: 600;
  padding: 10px 20px;
  border: none;
  border-radius: 8px;
  cursor: pointer;
  transition: all 0.15s ease;
}

.btn-primary:hover {
  filter: brightness(1.1);
  transform: translateY(-1px);
}

/* Secondary - Outlined */
.btn-secondary {
  background: transparent;
  color: var(--text-primary);
  border: 1px solid var(--border-default);
  padding: 10px 20px;
  border-radius: 8px;
  cursor: pointer;
}

.btn-secondary:hover {
  background: var(--bg-elevated);
  border-color: var(--fleek-blue);
}

/* Ghost - Minimal */
.btn-ghost {
  background: transparent;
  color: var(--text-secondary);
  border: none;
  padding: 8px 12px;
  border-radius: 6px;
}

.btn-ghost:hover {
  background: var(--bg-elevated);
  color: var(--text-primary);
}
```

---

## PureScript Types

```purescript
module UI.Brand.Fleek where

-- Brand color tokens
data FleekColor
  = Blue      -- #0090ff
  | Green     -- #32e48e
  | Yellow    -- #ffe629
  | Orange    -- #f76b15

-- Semantic status based on brand colors
data DiemStatus
  = Healthy   -- Green, >50%
  | Caution   -- Yellow, 25-50%
  | Warning   -- Orange, 10-25%
  | Critical  -- Red, <10%

fleekColorToHex :: FleekColor -> String
fleekColorToHex = case _ of
  Blue -> "#0090ff"
  Green -> "#32e48e"
  Yellow -> "#ffe629"
  Orange -> "#f76b15"

diemStatusColor :: DiemStatus -> String
diemStatusColor = case _ of
  Healthy -> fleekColorToHex Green
  Caution -> fleekColorToHex Yellow
  Warning -> fleekColorToHex Orange
  Critical -> "#ff4444"

-- Calculate status from percentage
diemPercentToStatus :: Number -> DiemStatus
diemPercentToStatus pct
  | pct > 50.0 = Healthy
  | pct > 25.0 = Caution
  | pct > 10.0 = Warning
  | otherwise = Critical
```

---

## Asset Manifest

```
/public/
├── fonts/
│   ├── Fraunces-Medium.ttf
│   └── Fraunces-SemiBold.ttf
├── images/
│   └── brand/
│       ├── fleek-logo.svg           # Full logo with wordmark
│       ├── flk-logo-on-light.svg    # Variant for light backgrounds
│       ├── circuit-banner-square.svg
│       ├── circuit-banner-wide.svg
│       ├── circuit-lines-only.svg
│       ├── circuit-pattern-dense.svg
│       ├── circuit-pattern-diagonal.svg
│       ├── circuit-pattern-minimal.svg
│       ├── fleek-grain-background.svg
│       ├── fleek-grain-overlay.svg
│       ├── fleek-grain-tile.svg
│       ├── rainbow-dots-pattern.svg
│       └── rainbow-gradient-bar.svg
└── icon.svg                         # Lightning bolt favicon
```

---

## Related Specifications

- `47-THEMING.md` - Theme implementation
- `50-DASHBOARD-LAYOUT.md` - Main layout
- `51-DIEM-TRACKER-WIDGET.md` - Balance display

---

*"Speed. Power. Fleek."*
