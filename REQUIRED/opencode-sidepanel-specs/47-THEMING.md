# 47-THEMING: Dark Mode and Terminal Aesthetic

## Overview

The sidepanel uses a dark theme by default, designed to complement terminal environments and reduce eye strain during long coding sessions. The theming system is built on CSS custom properties for easy customization.

---

## Design Principles

1. **Terminal-native** - Looks like it belongs next to a terminal
2. **Low contrast for comfort** - Not harsh black-on-white
3. **High contrast for readability** - Text is always legible
4. **Monospace everywhere** - JetBrains Mono as primary font
5. **Minimal decoration** - Focus on content, not chrome

---

## Color Palette

### Dark Theme (Default)

```css
:root {
  /* ─── Background Surfaces ─── */
  --color-bg-base: #0d0d0d;        /* Deepest background */
  --color-bg-surface: #1a1a1a;     /* Cards, panels */
  --color-bg-elevated: #242424;    /* Elevated cards, modals */
  --color-bg-hover: #2a2a2a;       /* Hover states */
  --color-bg-active: #333333;      /* Active/pressed states */
  
  /* ─── Text Colors ─── */
  --color-text-primary: #e4e4e7;   /* Primary text */
  --color-text-secondary: #a1a1aa; /* Secondary text, labels */
  --color-text-tertiary: #71717a;  /* Disabled, hints */
  --color-text-inverse: #18181b;   /* Text on light backgrounds */
  
  /* ─── Border Colors ─── */
  --color-border-subtle: #27272a;  /* Subtle separators */
  --color-border-default: #3f3f46; /* Default borders */
  --color-border-emphasis: #52525b;/* Emphasized borders */
  
  /* ─── Semantic Colors ─── */
  --color-primary: #3b82f6;        /* Primary actions, links */
  --color-primary-hover: #2563eb;  /* Primary hover */
  --color-primary-dim: rgba(59, 130, 246, 0.15); /* Primary background */
  
  --color-success: #22c55e;        /* Success states */
  --color-success-dim: rgba(34, 197, 94, 0.15);
  
  --color-warning: #f59e0b;        /* Warning states */
  --color-warning-dim: rgba(245, 158, 11, 0.15);
  
  --color-error: #ef4444;          /* Error states */
  --color-error-dim: rgba(239, 68, 68, 0.15);
  
  --color-info: #06b6d4;           /* Info states */
  --color-info-dim: rgba(6, 182, 212, 0.15);
  
  /* ─── Diem-specific Colors ─── */
  --color-diem: #8b5cf6;           /* Diem balance accent */
  --color-diem-dim: rgba(139, 92, 246, 0.15);
  
  /* ─── Code/Terminal Colors ─── */
  --color-code-bg: #0f0f0f;
  --color-code-border: #27272a;
}
```

### Light Theme (Optional)

```css
[data-theme="light"] {
  /* ─── Background Surfaces ─── */
  --color-bg-base: #ffffff;
  --color-bg-surface: #f4f4f5;
  --color-bg-elevated: #ffffff;
  --color-bg-hover: #e4e4e7;
  --color-bg-active: #d4d4d8;
  
  /* ─── Text Colors ─── */
  --color-text-primary: #18181b;
  --color-text-secondary: #52525b;
  --color-text-tertiary: #a1a1aa;
  --color-text-inverse: #fafafa;
  
  /* ─── Border Colors ─── */
  --color-border-subtle: #e4e4e7;
  --color-border-default: #d4d4d8;
  --color-border-emphasis: #a1a1aa;
  
  /* Semantic colors stay the same */
}
```

---

## Typography

### Font Stack

```css
:root {
  /* ─── Font Families ─── */
  --font-mono: 'JetBrains Mono', 'Fira Code', 'SF Mono', 
               'Consolas', 'Liberation Mono', monospace;
  --font-sans: -apple-system, BlinkMacSystemFont, 'Segoe UI', 
               Roboto, Oxygen, Ubuntu, sans-serif;
  
  /* ─── Font Sizes ─── */
  --font-size-xs: 11px;
  --font-size-sm: 12px;
  --font-size-base: 14px;
  --font-size-lg: 16px;
  --font-size-xl: 18px;
  --font-size-2xl: 24px;
  --font-size-3xl: 30px;
  
  /* ─── Font Weights ─── */
  --font-weight-normal: 400;
  --font-weight-medium: 500;
  --font-weight-semibold: 600;
  --font-weight-bold: 700;
  
  /* ─── Line Heights ─── */
  --line-height-tight: 1.25;
  --line-height-base: 1.5;
  --line-height-relaxed: 1.75;
  
  /* ─── Letter Spacing ─── */
  --letter-spacing-tight: -0.02em;
  --letter-spacing-normal: 0;
  --letter-spacing-wide: 0.02em;
  --letter-spacing-wider: 0.05em;
}
```

### Typography Classes

```css
/* Headings */
.text-heading-1 {
  font-family: var(--font-mono);
  font-size: var(--font-size-2xl);
  font-weight: var(--font-weight-bold);
  line-height: var(--line-height-tight);
  color: var(--color-text-primary);
}

.text-heading-2 {
  font-family: var(--font-mono);
  font-size: var(--font-size-xl);
  font-weight: var(--font-weight-semibold);
  line-height: var(--line-height-tight);
  color: var(--color-text-primary);
}

/* Labels */
.text-label {
  font-family: var(--font-mono);
  font-size: var(--font-size-xs);
  font-weight: var(--font-weight-semibold);
  letter-spacing: var(--letter-spacing-wider);
  text-transform: uppercase;
  color: var(--color-text-secondary);
}

/* Body text */
.text-body {
  font-family: var(--font-mono);
  font-size: var(--font-size-base);
  font-weight: var(--font-weight-normal);
  line-height: var(--line-height-base);
  color: var(--color-text-primary);
}

/* Numbers (tabular for alignment) */
.text-number {
  font-family: var(--font-mono);
  font-variant-numeric: tabular-nums;
  letter-spacing: var(--letter-spacing-tight);
}
```

---

## Spacing Scale

```css
:root {
  /* ─── Spacing ─── */
  --space-0: 0;
  --space-1: 4px;
  --space-2: 8px;
  --space-3: 12px;
  --space-4: 16px;
  --space-5: 20px;
  --space-6: 24px;
  --space-8: 32px;
  --space-10: 40px;
  --space-12: 48px;
  --space-16: 64px;
}
```

---

## Component Tokens

### Cards

```css
:root {
  --card-bg: var(--color-bg-surface);
  --card-border: var(--color-border-subtle);
  --card-border-radius: 8px;
  --card-padding: var(--space-4);
  --card-shadow: 0 1px 3px rgba(0, 0, 0, 0.1);
}

.card {
  background: var(--card-bg);
  border: 1px solid var(--card-border);
  border-radius: var(--card-border-radius);
  padding: var(--card-padding);
}
```

### Buttons

```css
:root {
  --button-height: 36px;
  --button-padding-x: var(--space-4);
  --button-border-radius: 6px;
  --button-font-size: var(--font-size-sm);
  --button-font-weight: var(--font-weight-medium);
}

.button {
  height: var(--button-height);
  padding: 0 var(--button-padding-x);
  border-radius: var(--button-border-radius);
  font-family: var(--font-mono);
  font-size: var(--button-font-size);
  font-weight: var(--button-font-weight);
  cursor: pointer;
  transition: all 0.15s ease;
}

.button--primary {
  background: var(--color-primary);
  color: white;
  border: none;
}

.button--primary:hover {
  background: var(--color-primary-hover);
}

.button--secondary {
  background: transparent;
  color: var(--color-text-primary);
  border: 1px solid var(--color-border-default);
}

.button--secondary:hover {
  background: var(--color-bg-hover);
  border-color: var(--color-border-emphasis);
}

.button--ghost {
  background: transparent;
  color: var(--color-text-secondary);
  border: none;
}

.button--ghost:hover {
  background: var(--color-bg-hover);
  color: var(--color-text-primary);
}
```

### Inputs

```css
:root {
  --input-height: 36px;
  --input-padding-x: var(--space-3);
  --input-border-radius: 6px;
  --input-bg: var(--color-bg-base);
  --input-border: var(--color-border-default);
  --input-border-focus: var(--color-primary);
}

.input {
  height: var(--input-height);
  padding: 0 var(--input-padding-x);
  background: var(--input-bg);
  border: 1px solid var(--input-border);
  border-radius: var(--input-border-radius);
  font-family: var(--font-mono);
  font-size: var(--font-size-base);
  color: var(--color-text-primary);
  outline: none;
  transition: border-color 0.15s ease;
}

.input:focus {
  border-color: var(--input-border-focus);
  box-shadow: 0 0 0 3px var(--color-primary-dim);
}

.input::placeholder {
  color: var(--color-text-tertiary);
}
```

---

## Alert Level Styling

### Balance Alerts

```css
/* Normal state */
.diem-tracker {
  background: var(--card-bg);
  border: 1px solid var(--card-border);
}

/* Warning state (< 20% or < 2h remaining) */
.diem-tracker--warning {
  border-color: var(--color-warning);
  background: linear-gradient(
    135deg,
    var(--card-bg) 0%,
    var(--color-warning-dim) 100%
  );
}

.diem-tracker--warning .countdown-time {
  color: var(--color-warning);
}

/* Critical state (< 5% or < 30min remaining) */
.diem-tracker--critical {
  border-color: var(--color-error);
  background: linear-gradient(
    135deg,
    var(--card-bg) 0%,
    var(--color-error-dim) 100%
  );
  animation: pulse-border 2s ease-in-out infinite;
}

.diem-tracker--critical .countdown-time {
  color: var(--color-error);
  animation: pulse-text 1s ease-in-out infinite;
}

@keyframes pulse-border {
  0%, 100% { border-color: var(--color-error); }
  50% { border-color: rgba(239, 68, 68, 0.5); }
}

@keyframes pulse-text {
  0%, 100% { opacity: 1; }
  50% { opacity: 0.7; }
}

/* Depleted state */
.diem-tracker--depleted {
  border-color: var(--color-error);
  background: var(--color-error-dim);
}
```

---

## Theme Switching

### PureScript Implementation

```purescript
module Sidepanel.Utils.Theme where

import Effect (Effect)
import Web.HTML (window)
import Web.HTML.Window (localStorage)
import Web.Storage.Storage (getItem, setItem)

data Theme = Dark | Light

derive instance eqTheme :: Eq Theme

-- Get current theme
getTheme :: Effect Theme
getTheme = do
  storage <- localStorage =<< window
  stored <- getItem "theme" storage
  pure $ case stored of
    Just "light" -> Light
    _ -> Dark

-- Set theme
setTheme :: Theme -> Effect Unit
setTheme theme = do
  storage <- localStorage =<< window
  setItem "theme" (themeToString theme) storage
  applyTheme theme

-- Apply theme to document
applyTheme :: Theme -> Effect Unit
applyTheme theme = do
  doc <- document =<< window
  let root = documentElement doc
  setAttribute "data-theme" (themeToString theme) root

themeToString :: Theme -> String
themeToString Dark = "dark"
themeToString Light = "light"

-- Toggle between themes
toggleTheme :: Effect Theme
toggleTheme = do
  current <- getTheme
  let next = case current of
        Dark -> Light
        Light -> Dark
  setTheme next
  pure next
```

### CSS Theme Application

```css
/* Default (dark) */
:root {
  /* dark theme variables */
}

/* Light theme override */
[data-theme="light"] {
  /* light theme variables */
}

/* System preference */
@media (prefers-color-scheme: light) {
  [data-theme="system"] {
    /* light theme variables */
  }
}
```

---

## Animation Guidelines

### Transitions

```css
:root {
  --transition-fast: 0.1s ease;
  --transition-base: 0.15s ease;
  --transition-slow: 0.3s ease;
}

/* Use transitions for */
.interactive {
  transition: 
    background var(--transition-fast),
    border-color var(--transition-fast),
    color var(--transition-fast),
    opacity var(--transition-base),
    transform var(--transition-base);
}
```

### Animation Principles

1. **Subtle** - Animations should be barely noticeable
2. **Fast** - Never more than 300ms
3. **Purposeful** - Only animate to convey state change
4. **Respectful** - Honor `prefers-reduced-motion`

```css
/* Respect reduced motion preference */
@media (prefers-reduced-motion: reduce) {
  *,
  *::before,
  *::after {
    animation-duration: 0.01ms !important;
    animation-iteration-count: 1 !important;
    transition-duration: 0.01ms !important;
  }
}
```

---

## Scrollbars

```css
/* Custom scrollbars for dark theme */
::-webkit-scrollbar {
  width: 8px;
  height: 8px;
}

::-webkit-scrollbar-track {
  background: var(--color-bg-base);
}

::-webkit-scrollbar-thumb {
  background: var(--color-border-default);
  border-radius: 4px;
}

::-webkit-scrollbar-thumb:hover {
  background: var(--color-border-emphasis);
}

/* Firefox */
* {
  scrollbar-width: thin;
  scrollbar-color: var(--color-border-default) var(--color-bg-base);
}
```

---

## Related Specifications

- `48-KEYBOARD-NAVIGATION.md` - Keyboard interaction
- `51-DIEM-TRACKER-WIDGET.md` - Widget styling
- `85-CODE-STYLE-GUIDE.md` - CSS conventions

---

*"Good design is invisible. Great dark themes are invisible at 2 AM."*
