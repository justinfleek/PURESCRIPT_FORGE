# 94-FLEEK-CSS-TOKENS: Complete Design Token System

## Overview

This specification provides the complete CSS custom property system for the Fleek-branded OpenCode Sidepanel.

---

## Complete Token File

```css
/* frontend/src/styles/tokens.css */

:root {
  /* ═══════════════════════════════════════════════════════════════════════
     FLEEK BRAND COLORS
     ═══════════════════════════════════════════════════════════════════════ */
  
  /* Primary Rainbow Gradient Colors */
  --fleek-blue: #0090ff;
  --fleek-green: #32e48e;
  --fleek-yellow: #ffe629;
  --fleek-orange: #f76b15;
  
  /* Rainbow Gradients */
  --gradient-rainbow: linear-gradient(90deg, 
    var(--fleek-blue) 0%, 
    var(--fleek-green) 33%, 
    var(--fleek-yellow) 66%, 
    var(--fleek-orange) 100%
  );
  
  --gradient-rainbow-vertical: linear-gradient(180deg,
    var(--fleek-blue) 0%,
    var(--fleek-green) 33%,
    var(--fleek-yellow) 66%,
    var(--fleek-orange) 100%
  );
  
  --gradient-rainbow-diagonal: linear-gradient(135deg,
    var(--fleek-blue) 0%,
    var(--fleek-green) 33%,
    var(--fleek-yellow) 66%,
    var(--fleek-orange) 100%
  );

  /* ═══════════════════════════════════════════════════════════════════════
     BACKGROUND COLORS
     ═══════════════════════════════════════════════════════════════════════ */
  
  --bg-base: #0a0a0a;
  --bg-surface: #111111;
  --bg-elevated: #1a1a1a;
  --bg-overlay: #222222;
  --bg-hover: #2a2a2a;
  --bg-active: #333333;
  
  /* Translucent backgrounds */
  --bg-glass: rgba(17, 17, 17, 0.8);
  --bg-modal: rgba(0, 0, 0, 0.8);
  --bg-tooltip: rgba(34, 34, 34, 0.95);

  /* ═══════════════════════════════════════════════════════════════════════
     TEXT COLORS
     ═══════════════════════════════════════════════════════════════════════ */
  
  --text-primary: #ffffff;
  --text-secondary: #a0a0a0;
  --text-tertiary: #666666;
  --text-disabled: #444444;
  --text-inverse: #0a0a0a;
  
  /* Accent text */
  --text-accent-blue: var(--fleek-blue);
  --text-accent-green: var(--fleek-green);
  --text-accent-yellow: var(--fleek-yellow);
  --text-accent-orange: var(--fleek-orange);

  /* ═══════════════════════════════════════════════════════════════════════
     BORDER COLORS
     ═══════════════════════════════════════════════════════════════════════ */
  
  --border-subtle: #1f1f1f;
  --border-default: #333333;
  --border-strong: #444444;
  --border-focus: var(--fleek-blue);
  
  /* Accent borders */
  --border-accent-blue: var(--fleek-blue);
  --border-accent-green: var(--fleek-green);

  /* ═══════════════════════════════════════════════════════════════════════
     SEMANTIC COLORS
     ═══════════════════════════════════════════════════════════════════════ */
  
  /* Status */
  --color-success: var(--fleek-green);
  --color-warning: var(--fleek-yellow);
  --color-error: #ff4444;
  --color-info: var(--fleek-blue);
  
  /* Diem balance states */
  --diem-healthy: var(--fleek-green);
  --diem-caution: var(--fleek-yellow);
  --diem-warning: var(--fleek-orange);
  --diem-critical: var(--color-error);
  
  /* Connection states */
  --connection-connected: var(--fleek-green);
  --connection-connecting: var(--fleek-yellow);
  --connection-disconnected: var(--color-error);
  --connection-reconnecting: var(--fleek-orange);

  /* ═══════════════════════════════════════════════════════════════════════
     TYPOGRAPHY
     ═══════════════════════════════════════════════════════════════════════ */
  
  /* Font families */
  --font-display: 'Fraunces', Georgia, 'Times New Roman', serif;
  --font-body: 'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif;
  --font-mono: 'JetBrains Mono', 'Fira Code', 'SF Mono', Consolas, monospace;
  
  /* Font sizes */
  --text-xs: 0.75rem;    /* 12px */
  --text-sm: 0.875rem;   /* 14px */
  --text-base: 1rem;     /* 16px */
  --text-lg: 1.125rem;   /* 18px */
  --text-xl: 1.25rem;    /* 20px */
  --text-2xl: 1.5rem;    /* 24px */
  --text-3xl: 2rem;      /* 32px */
  --text-4xl: 2.5rem;    /* 40px */
  
  /* Font weights */
  --font-normal: 400;
  --font-medium: 500;
  --font-semibold: 600;
  --font-bold: 700;
  
  /* Line heights */
  --leading-none: 1;
  --leading-tight: 1.25;
  --leading-snug: 1.375;
  --leading-normal: 1.5;
  --leading-relaxed: 1.625;
  
  /* Letter spacing */
  --tracking-tight: -0.025em;
  --tracking-normal: 0;
  --tracking-wide: 0.025em;
  --tracking-wider: 0.05em;
  --tracking-widest: 0.1em;

  /* ═══════════════════════════════════════════════════════════════════════
     SPACING
     ═══════════════════════════════════════════════════════════════════════ */
  
  --space-0: 0;
  --space-1: 0.25rem;   /* 4px */
  --space-2: 0.5rem;    /* 8px */
  --space-3: 0.75rem;   /* 12px */
  --space-4: 1rem;      /* 16px */
  --space-5: 1.25rem;   /* 20px */
  --space-6: 1.5rem;    /* 24px */
  --space-8: 2rem;      /* 32px */
  --space-10: 2.5rem;   /* 40px */
  --space-12: 3rem;     /* 48px */
  --space-16: 4rem;     /* 64px */
  --space-20: 5rem;     /* 80px */
  --space-24: 6rem;     /* 96px */

  /* ═══════════════════════════════════════════════════════════════════════
     BORDER RADIUS
     ═══════════════════════════════════════════════════════════════════════ */
  
  --radius-none: 0;
  --radius-sm: 0.25rem;   /* 4px */
  --radius-default: 0.5rem;  /* 8px */
  --radius-md: 0.75rem;   /* 12px */
  --radius-lg: 1rem;      /* 16px */
  --radius-xl: 1.5rem;    /* 24px */
  --radius-full: 9999px;

  /* ═══════════════════════════════════════════════════════════════════════
     SHADOWS
     ═══════════════════════════════════════════════════════════════════════ */
  
  --shadow-sm: 0 1px 2px 0 rgba(0, 0, 0, 0.5);
  --shadow-default: 0 2px 4px 0 rgba(0, 0, 0, 0.5);
  --shadow-md: 0 4px 8px 0 rgba(0, 0, 0, 0.5);
  --shadow-lg: 0 8px 16px 0 rgba(0, 0, 0, 0.5);
  --shadow-xl: 0 16px 32px 0 rgba(0, 0, 0, 0.5);
  
  /* Glow effects for accents */
  --glow-blue: 0 0 20px rgba(0, 144, 255, 0.3);
  --glow-green: 0 0 20px rgba(50, 228, 142, 0.3);
  --glow-yellow: 0 0 20px rgba(255, 230, 41, 0.3);
  --glow-orange: 0 0 20px rgba(247, 107, 21, 0.3);

  /* ═══════════════════════════════════════════════════════════════════════
     TRANSITIONS
     ═══════════════════════════════════════════════════════════════════════ */
  
  --duration-instant: 0ms;
  --duration-fast: 100ms;
  --duration-normal: 200ms;
  --duration-slow: 300ms;
  --duration-slower: 500ms;
  
  --ease-linear: linear;
  --ease-in: cubic-bezier(0.4, 0, 1, 1);
  --ease-out: cubic-bezier(0, 0, 0.2, 1);
  --ease-in-out: cubic-bezier(0.4, 0, 0.2, 1);
  --ease-bounce: cubic-bezier(0.68, -0.55, 0.265, 1.55);

  /* ═══════════════════════════════════════════════════════════════════════
     Z-INDEX LAYERS
     ═══════════════════════════════════════════════════════════════════════ */
  
  --z-base: 0;
  --z-dropdown: 100;
  --z-sticky: 200;
  --z-fixed: 300;
  --z-modal-backdrop: 400;
  --z-modal: 500;
  --z-popover: 600;
  --z-tooltip: 700;
  --z-toast: 800;
  --z-command-palette: 900;

  /* ═══════════════════════════════════════════════════════════════════════
     LAYOUT
     ═══════════════════════════════════════════════════════════════════════ */
  
  /* Sidebar widths */
  --sidebar-collapsed: 64px;
  --sidebar-expanded: 280px;
  
  /* Panel sizes */
  --panel-sm: 320px;
  --panel-md: 480px;
  --panel-lg: 640px;
  
  /* Header height */
  --header-height: 56px;
  
  /* Content constraints */
  --content-max-width: 1200px;
  --content-padding: var(--space-6);

  /* ═══════════════════════════════════════════════════════════════════════
     COMPONENT-SPECIFIC TOKENS
     ═══════════════════════════════════════════════════════════════════════ */
  
  /* Button */
  --btn-height-sm: 32px;
  --btn-height-md: 40px;
  --btn-height-lg: 48px;
  --btn-padding-x: var(--space-4);
  --btn-radius: var(--radius-default);
  
  /* Input */
  --input-height: 40px;
  --input-padding-x: var(--space-3);
  --input-radius: var(--radius-default);
  --input-border: var(--border-default);
  --input-focus-ring: 0 0 0 2px var(--fleek-blue);
  
  /* Card */
  --card-padding: var(--space-4);
  --card-radius: var(--radius-md);
  --card-bg: var(--bg-surface);
  --card-border: var(--border-subtle);
  
  /* Toast */
  --toast-width: 360px;
  --toast-padding: var(--space-4);
  --toast-radius: var(--radius-default);
  
  /* Rainbow bar */
  --rainbow-bar-height: 4px;
  
  /* Diem widget */
  --diem-progress-height: 8px;
  --diem-value-size: var(--text-4xl);
}

/* ═══════════════════════════════════════════════════════════════════════
   DARK/LIGHT MODE OVERRIDES (if ever needed)
   ═══════════════════════════════════════════════════════════════════════ */

@media (prefers-color-scheme: light) {
  :root.auto-theme {
    /* Light mode would go here - but we're dark-first */
  }
}

/* ═══════════════════════════════════════════════════════════════════════
   ANIMATIONS
   ═══════════════════════════════════════════════════════════════════════ */

@keyframes rainbow-shift {
  0% { background-position: 0% 50%; }
  100% { background-position: 200% 50%; }
}

@keyframes pulse-green {
  0%, 100% { box-shadow: 0 0 0 0 rgba(50, 228, 142, 0.4); }
  50% { box-shadow: 0 0 0 8px rgba(50, 228, 142, 0); }
}

@keyframes pulse-yellow {
  0%, 100% { box-shadow: 0 0 0 0 rgba(255, 230, 41, 0.4); }
  50% { box-shadow: 0 0 0 8px rgba(255, 230, 41, 0); }
}

@keyframes pulse-red {
  0%, 100% { box-shadow: 0 0 0 0 rgba(255, 68, 68, 0.4); }
  50% { box-shadow: 0 0 0 8px rgba(255, 68, 68, 0); }
}

@keyframes fade-in {
  from { opacity: 0; }
  to { opacity: 1; }
}

@keyframes slide-up {
  from { 
    opacity: 0;
    transform: translateY(10px);
  }
  to {
    opacity: 1;
    transform: translateY(0);
  }
}

@keyframes slide-down {
  from {
    opacity: 0;
    transform: translateY(-10px);
  }
  to {
    opacity: 1;
    transform: translateY(0);
  }
}

@keyframes spin {
  from { transform: rotate(0deg); }
  to { transform: rotate(360deg); }
}

/* ═══════════════════════════════════════════════════════════════════════
   UTILITY CLASSES
   ═══════════════════════════════════════════════════════════════════════ */

.fleek-rainbow-bar {
  height: var(--rainbow-bar-height);
  background: var(--gradient-rainbow);
  width: 100%;
}

.fleek-rainbow-bar--animated {
  background-size: 200% 100%;
  animation: rainbow-shift 2s linear infinite;
}

.fleek-circuit-bg {
  background-image: url('/images/brand/circuit-pattern-minimal.svg');
  background-repeat: repeat;
  background-size: 200px;
  opacity: 0.03;
}

.fleek-grain {
  background-image: url('/images/brand/fleek-grain-tile.svg');
  background-repeat: repeat;
  opacity: 0.02;
  mix-blend-mode: overlay;
}

/* Status indicators */
.status-healthy { color: var(--diem-healthy); }
.status-caution { color: var(--diem-caution); }
.status-warning { color: var(--diem-warning); }
.status-critical { color: var(--diem-critical); }

/* Glow effects */
.glow-blue { box-shadow: var(--glow-blue); }
.glow-green { box-shadow: var(--glow-green); }
.glow-yellow { box-shadow: var(--glow-yellow); }
.glow-orange { box-shadow: var(--glow-orange); }
```

---

## Usage Examples

### Diem Progress Bar

```css
.diem-progress {
  height: var(--diem-progress-height);
  border-radius: var(--radius-full);
  background: var(--bg-overlay);
  overflow: hidden;
}

.diem-progress__fill {
  height: 100%;
  background: var(--gradient-rainbow);
  transition: width var(--duration-slow) var(--ease-out);
}

.diem-progress__fill[data-status="healthy"] {
  background: var(--diem-healthy);
}

.diem-progress__fill[data-status="caution"] {
  background: var(--diem-caution);
}

.diem-progress__fill[data-status="warning"] {
  background: var(--diem-warning);
}

.diem-progress__fill[data-status="critical"] {
  background: var(--diem-critical);
  animation: pulse-red 1.5s ease-in-out infinite;
}
```

### Session Tab

```css
.session-tab {
  background: var(--card-bg);
  border: 1px solid var(--card-border);
  border-radius: var(--card-radius);
  padding: var(--space-3) var(--space-4);
  transition: all var(--duration-fast) var(--ease-out);
}

.session-tab:hover {
  background: var(--bg-hover);
  border-color: var(--border-default);
}

.session-tab--active {
  background: var(--bg-elevated);
  border-color: var(--fleek-blue);
}

.session-tab--active::after {
  content: '';
  position: absolute;
  bottom: 0;
  left: 0;
  right: 0;
  height: 2px;
  background: var(--gradient-rainbow);
}
```

---

## Related Specifications

- `90-FLEEK-BRAND-INTEGRATION.md` - Brand guidelines
- `47-THEMING.md` - Theme implementation
- `85-CODE-STYLE-GUIDE.md` - Code conventions

---

*"Consistent tokens, consistent experience."*
