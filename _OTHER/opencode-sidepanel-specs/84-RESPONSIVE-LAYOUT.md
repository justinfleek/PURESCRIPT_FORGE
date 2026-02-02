# 84-RESPONSIVE-LAYOUT: Adaptive Design for All Screen Sizes

## Overview

The sidepanel adapts to different screen sizes and contexts: docked sidebar mode, floating window, tablet, and mobile. This document defines breakpoints, layout adaptations, and touch-friendly interactions.

---

## Display Contexts

1. **Docked Sidebar** (300-400px) - Primary use case, beside editor
2. **Floating Window** (400-800px) - Standalone window
3. **Tablet** (768-1024px) - Full-width with touch
4. **Mobile** (320-767px) - Single-column, bottom sheet modals

---

## Breakpoints

```css
:root {
  /* Sidebar widths */
  --sidebar-min: 300px;
  --sidebar-default: 360px;
  --sidebar-max: 480px;
  
  /* Responsive breakpoints */
  --bp-mobile: 320px;
  --bp-mobile-lg: 480px;
  --bp-tablet: 768px;
  --bp-desktop: 1024px;
  --bp-wide: 1440px;
}

/* Breakpoint mixins (in SCSS) */
@mixin mobile {
  @media (max-width: 767px) { @content; }
}

@mixin tablet {
  @media (min-width: 768px) and (max-width: 1023px) { @content; }
}

@mixin desktop {
  @media (min-width: 1024px) { @content; }
}

@mixin sidebar {
  @media (max-width: 480px) { @content; }
}
```

---

## Layout Modes

### Sidebar Mode (Default)

```
┌─────────────────────────────────────────┐
│ ┌─────┬──────────────────────────────┐ │
│ │ NAV │  CONTENT                     │ │
│ │     │                              │ │
│ │ ○   │  ┌────────────────────────┐ │ │
│ │ ○   │  │ Widget 1               │ │ │
│ │ ○   │  └────────────────────────┘ │ │
│ │ ○   │                              │ │
│ │ ○   │  ┌────────────────────────┐ │ │
│ │     │  │ Widget 2               │ │ │
│ │     │  └────────────────────────┘ │ │
│ │     │                              │ │
│ └─────┴──────────────────────────────┘ │
│         300-400px                      │
└─────────────────────────────────────────┘
```

### Floating Window Mode

```
┌─────────────────────────────────────────────────────────────┐
│ ┌─────────────────────────────────────────────────────────┐ │
│ │ NAV                    CONTENT                          │ │
│ │                                                         │ │
│ │ ○ Dashboard            ┌──────────┐  ┌──────────┐      │ │
│ │ ○ Session              │ Widget 1 │  │ Widget 2 │      │ │
│ │ ○ Proofs               └──────────┘  └──────────┘      │ │
│ │ ○ Timeline                                              │ │
│ │ ○ Settings             ┌─────────────────────────┐     │ │
│ │                        │ Widget 3                │     │ │
│ │                        └─────────────────────────┘     │ │
│ └─────────────────────────────────────────────────────────┘ │
│                     500-800px                               │
└─────────────────────────────────────────────────────────────┘
```

### Mobile Mode

```
┌─────────────────────────┐
│ ┌─────────────────────┐ │
│ │  ≡  Dashboard    ⚙  │ │  ← Header with menu
│ ├─────────────────────┤ │
│ │                     │ │
│ │  ┌───────────────┐  │ │
│ │  │   Balance     │  │ │  ← Full-width widgets
│ │  │   42.5 Diem   │  │ │
│ │  └───────────────┘  │ │
│ │                     │ │
│ │  ┌───────────────┐  │ │
│ │  │   Countdown   │  │ │
│ │  │   4h 23m      │  │ │
│ │  └───────────────┘  │ │
│ │                     │ │
│ │  ┌───────────────┐  │ │
│ │  │   Session     │  │ │
│ │  │   Debug Auth  │  │ │
│ │  └───────────────┘  │ │
│ │                     │ │
│ └─────────────────────┘ │
│                         │
│ ┌─────────────────────┐ │
│ │ ○   ○   ●   ○   ○   │ │  ← Bottom navigation
│ └─────────────────────┘ │
└─────────────────────────┘
        320-480px
```

---

## Component Adaptations

### Dashboard

```css
.dashboard {
  display: grid;
  gap: var(--space-4);
  padding: var(--space-4);
}

/* Sidebar mode: single column */
@media (max-width: 480px) {
  .dashboard {
    grid-template-columns: 1fr;
  }
}

/* Floating/tablet: two columns */
@media (min-width: 481px) and (max-width: 1023px) {
  .dashboard {
    grid-template-columns: repeat(2, 1fr);
  }
  
  .dashboard__widget--full {
    grid-column: span 2;
  }
}

/* Wide: three columns */
@media (min-width: 1024px) {
  .dashboard {
    grid-template-columns: repeat(3, 1fr);
  }
  
  .dashboard__widget--full {
    grid-column: span 3;
  }
}
```

### Navigation

```css
/* Sidebar mode: icon-only navigation */
@media (max-width: 360px) {
  .sidebar-nav {
    width: 48px;
  }
  
  .sidebar-nav__label {
    display: none;
  }
  
  .sidebar-nav__item {
    justify-content: center;
    padding: var(--space-3);
  }
}

/* Mobile: bottom tab bar */
@media (max-width: 767px) {
  .sidebar-nav {
    position: fixed;
    bottom: 0;
    left: 0;
    right: 0;
    flex-direction: row;
    justify-content: space-around;
    width: 100%;
    height: 56px;
    border-top: 1px solid var(--color-border-default);
    background: var(--color-bg-surface);
    z-index: 100;
  }
  
  .sidebar-nav__item {
    flex-direction: column;
    gap: 2px;
    padding: var(--space-1);
  }
  
  .sidebar-nav__label {
    font-size: 10px;
  }
  
  /* Add bottom padding to content */
  .main-content {
    padding-bottom: 72px;
  }
}
```

### Modals

```css
/* Mobile: bottom sheet style */
@media (max-width: 767px) {
  .modal-overlay {
    align-items: flex-end;
    padding: 0;
  }
  
  .modal {
    width: 100%;
    max-width: 100%;
    max-height: 90vh;
    border-radius: 16px 16px 0 0;
    animation: slideUp 0.3s ease-out;
  }
  
  @keyframes slideUp {
    from {
      transform: translateY(100%);
    }
    to {
      transform: translateY(0);
    }
  }
}
```

### Charts

```css
.chart-container {
  width: 100%;
  height: 200px;
}

/* Sidebar: smaller charts */
@media (max-width: 400px) {
  .chart-container {
    height: 150px;
  }
  
  .chart-container--mini {
    height: 80px;
  }
}

/* Tablet+: larger charts */
@media (min-width: 768px) {
  .chart-container {
    height: 300px;
  }
}
```

---

## Touch Interactions

### Touch Targets

```css
/* Minimum 44x44px touch targets (WCAG) */
@media (pointer: coarse) {
  .btn,
  .nav-item,
  .list-item,
  .icon-button {
    min-height: 44px;
    min-width: 44px;
  }
  
  .btn--sm {
    min-height: 36px;
    padding: var(--space-2) var(--space-3);
  }
  
  /* Increase spacing for touch */
  .list-item {
    padding: var(--space-3) var(--space-4);
  }
}
```

### Swipe Gestures (Mobile)

```typescript
// Swipe to dismiss notifications
interface SwipeConfig {
  threshold: number;      // Min distance to trigger
  velocityThreshold: number;
  direction: 'left' | 'right' | 'up' | 'down';
  onSwipe: () => void;
}

function useSwipeGesture(element: HTMLElement, config: SwipeConfig): void {
  let startX = 0;
  let startY = 0;
  let startTime = 0;
  
  element.addEventListener('touchstart', (e) => {
    startX = e.touches[0].clientX;
    startY = e.touches[0].clientY;
    startTime = Date.now();
  });
  
  element.addEventListener('touchend', (e) => {
    const endX = e.changedTouches[0].clientX;
    const endY = e.changedTouches[0].clientY;
    const duration = Date.now() - startTime;
    
    const deltaX = endX - startX;
    const deltaY = endY - startY;
    const velocity = Math.abs(deltaX) / duration;
    
    if (config.direction === 'right' && 
        deltaX > config.threshold && 
        velocity > config.velocityThreshold) {
      config.onSwipe();
    }
  });
}
```

### Pull to Refresh

```purescript
-- Mobile pull-to-refresh
type PullToRefreshState =
  { isPulling :: Boolean
  , pullDistance :: Number
  , isRefreshing :: Boolean
  }

handleTouchMove :: TouchEvent -> State -> State
handleTouchMove event state
  | state.scrollTop == 0 && not state.isRefreshing =
      let distance = event.touches[0].clientY - state.touchStartY
      in state { isPulling = distance > 0, pullDistance = min 100.0 distance }
  | otherwise = state

handleTouchEnd :: State -> Effect State
handleTouchEnd state
  | state.pullDistance > 60.0 = do
      triggerRefresh
      pure state { isRefreshing = true, isPulling = false }
  | otherwise = 
      pure state { isPulling = false, pullDistance = 0.0 }
```

---

## Typography Scaling

```css
:root {
  /* Base size scales with viewport */
  --font-size-base: clamp(14px, 2.5vw, 16px);
}

/* Heading scales */
h1 { font-size: clamp(1.5rem, 4vw, 2rem); }
h2 { font-size: clamp(1.25rem, 3vw, 1.5rem); }
h3 { font-size: clamp(1.1rem, 2.5vw, 1.25rem); }

/* Sidebar: slightly smaller text */
@media (max-width: 400px) {
  :root {
    --font-size-base: 13px;
    --font-size-sm: 11px;
    --font-size-xs: 10px;
  }
}
```

---

## Responsive Images/Charts

```purescript
-- Render different chart types based on viewport
renderChart :: Viewport -> ChartData -> H.ComponentHTML Action () m
renderChart viewport data_ = case viewport of
  Mobile -> renderMiniChart data_      -- Sparkline only
  Sidebar -> renderCompactChart data_  -- Simple line chart
  Tablet -> renderFullChart data_      -- Full featured
  Desktop -> renderFullChart data_     -- Full featured

-- Viewport detection
foreign import getViewport :: Effect Viewport

data Viewport
  = Mobile    -- < 480px
  | Sidebar   -- 480-767px
  | Tablet    -- 768-1023px
  | Desktop   -- >= 1024px
```

---

## Collapsible Sections

```css
/* Mobile: collapsible sections to save space */
@media (max-width: 767px) {
  .collapsible-section {
    border-bottom: 1px solid var(--color-border-subtle);
  }
  
  .collapsible-section__header {
    display: flex;
    align-items: center;
    justify-content: space-between;
    padding: var(--space-3) var(--space-4);
    cursor: pointer;
  }
  
  .collapsible-section__content {
    padding: 0 var(--space-4) var(--space-4);
    display: none;
  }
  
  .collapsible-section--expanded .collapsible-section__content {
    display: block;
  }
  
  .collapsible-section__toggle {
    transition: transform 0.2s;
  }
  
  .collapsible-section--expanded .collapsible-section__toggle {
    transform: rotate(180deg);
  }
}

/* Desktop: always expanded */
@media (min-width: 768px) {
  .collapsible-section__header {
    cursor: default;
  }
  
  .collapsible-section__toggle {
    display: none;
  }
  
  .collapsible-section__content {
    display: block;
  }
}
```

---

## Testing Responsive

### Viewport Sizes to Test

| Device | Width | Height |
|--------|-------|--------|
| iPhone SE | 375px | 667px |
| iPhone 14 | 390px | 844px |
| iPad Mini | 768px | 1024px |
| iPad Pro | 1024px | 1366px |
| Sidebar (min) | 300px | 800px |
| Sidebar (default) | 360px | 800px |
| Floating | 600px | 800px |

### Testing Checklist

- [ ] All content accessible at 300px width
- [ ] Touch targets ≥44px on mobile
- [ ] No horizontal scroll
- [ ] Text readable without zoom
- [ ] Charts scale properly
- [ ] Modals work as bottom sheets
- [ ] Navigation accessible at all sizes
- [ ] Forms usable on mobile

---

## Related Specifications

- `50-DASHBOARD-LAYOUT.md` - Dashboard structure
- `49-SIDEBAR-NAVIGATION.md` - Navigation component
- `43-ACCESSIBILITY.md` - Touch accessibility

---

*"Design for the smallest screen first. Scale up from there."*
