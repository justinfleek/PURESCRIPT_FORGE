# 43-ACCESSIBILITY: WCAG Compliance and Inclusive Design

## Overview

The sidepanel is designed to be fully accessible, meeting WCAG 2.1 AA standards. This document covers keyboard navigation, screen reader support, color contrast, focus management, and assistive technology compatibility.

---

## Accessibility Principles

1. **Perceivable** - Information presentable in ways all users can perceive
2. **Operable** - All functionality available via keyboard
3. **Understandable** - Predictable, clear interface
4. **Robust** - Compatible with assistive technologies

---

## Keyboard Navigation

### Global Shortcuts

| Key | Action | Context |
|-----|--------|---------|
| `Tab` | Next focusable element | Global |
| `Shift+Tab` | Previous focusable element | Global |
| `Enter`/`Space` | Activate focused element | Global |
| `Escape` | Close modal/menu, cancel action | Global |
| `?` | Open keyboard shortcuts help | Global |
| `Ctrl+Shift+P` | Command palette | Global |
| `/` | Focus search | Global |

### Navigation Keys

| Key | Action |
|-----|--------|
| `1-5` | Jump to view (Dashboard, Session, etc.) |
| `j`/`↓` | Move down in list |
| `k`/`↑` | Move up in list |
| `h`/`←` | Collapse/move left |
| `l`/`→` | Expand/move right |
| `gg` | Go to first item |
| `G` | Go to last item |
| `Ctrl+d` | Page down |
| `Ctrl+u` | Page up |

### Focus Management

```typescript
// Focus trap for modals
function trapFocus(container: HTMLElement): () => void {
  const focusableElements = container.querySelectorAll(
    'button, [href], input, select, textarea, [tabindex]:not([tabindex="-1"])'
  );
  
  const first = focusableElements[0] as HTMLElement;
  const last = focusableElements[focusableElements.length - 1] as HTMLElement;
  
  const handleKeyDown = (e: KeyboardEvent) => {
    if (e.key !== 'Tab') return;
    
    if (e.shiftKey && document.activeElement === first) {
      e.preventDefault();
      last.focus();
    } else if (!e.shiftKey && document.activeElement === last) {
      e.preventDefault();
      first.focus();
    }
  };
  
  container.addEventListener('keydown', handleKeyDown);
  first.focus();
  
  return () => container.removeEventListener('keydown', handleKeyDown);
}
```

---

## Screen Reader Support

### ARIA Landmarks

```html
<div role="application" aria-label="OpenCode Sidepanel">
  <nav role="navigation" aria-label="Main navigation">
    <!-- Sidebar navigation -->
  </nav>
  
  <main role="main" aria-label="Main content">
    <!-- View content -->
  </main>
  
  <aside role="complementary" aria-label="Session details">
    <!-- Session panel -->
  </aside>
  
  <div role="status" aria-live="polite" aria-label="Notifications">
    <!-- Toast notifications -->
  </div>
</div>
```

### Live Regions

```purescript
-- Announce balance changes
renderBalanceUpdate :: Number -> H.ComponentHTML Action () m
renderBalanceUpdate balance =
  HH.div
    [ HP.attr (H.AttrName "role") "status"
    , HP.attr (H.AttrName "aria-live") "polite"
    , HP.attr (H.AttrName "aria-atomic") "true"
    ]
    [ HH.text $ "Balance updated: " <> formatDiem balance <> " Diem remaining" ]

-- Announce errors immediately
renderError :: String -> H.ComponentHTML Action () m
renderError message =
  HH.div
    [ HP.attr (H.AttrName "role") "alert"
    , HP.attr (H.AttrName "aria-live") "assertive"
    ]
    [ HH.text message ]
```

### ARIA Labels

```purescript
-- Button with icon only
HH.button
  [ HP.class_ (H.ClassName "icon-button")
  , HP.attr (H.AttrName "aria-label") "Create new session"
  , HP.title "Create new session (Ctrl+N)"
  ]
  [ HH.text "+" ]

-- Progress bar
HH.div
  [ HP.class_ (H.ClassName "progress-bar")
  , HP.attr (H.AttrName "role") "progressbar"
  , HP.attr (H.AttrName "aria-valuenow") (show percentage)
  , HP.attr (H.AttrName "aria-valuemin") "0"
  , HP.attr (H.AttrName "aria-valuemax") "100"
  , HP.attr (H.AttrName "aria-label") "Diem balance: 42% remaining"
  ]
  []

-- Expandable section
HH.button
  [ HP.attr (H.AttrName "aria-expanded") (if expanded then "true" else "false")
  , HP.attr (H.AttrName "aria-controls") "section-content"
  ]
  [ HH.text "Session Details" ]
```

---

## Color Contrast

### Minimum Contrast Ratios (WCAG AA)

| Element | Ratio Required | Our Ratio |
|---------|---------------|-----------|
| Normal text | 4.5:1 | 7.2:1 |
| Large text (18px+) | 3:1 | 5.8:1 |
| UI components | 3:1 | 4.1:1 |
| Focus indicators | 3:1 | 4.5:1 |

### Color Palette Accessibility

```css
:root {
  /* Primary colors - tested for contrast */
  --color-text-primary: #e4e4e7;     /* On dark: 12.6:1 */
  --color-text-secondary: #a1a1aa;   /* On dark: 7.2:1 */
  --color-text-tertiary: #71717a;    /* On dark: 4.5:1 */
  
  /* Status colors - distinct and accessible */
  --color-success: #22c55e;          /* Green, 4.5:1 */
  --color-warning: #f59e0b;          /* Amber, 4.5:1 */
  --color-error: #ef4444;            /* Red, 4.6:1 */
  --color-info: #3b82f6;             /* Blue, 4.5:1 */
  
  /* Focus - high visibility */
  --color-focus: #8b5cf6;            /* Purple, 4.5:1 */
  --color-focus-ring: rgba(139, 92, 246, 0.5);
}
```

### Don't Rely on Color Alone

```purescript
-- Status with icon AND color
renderStatus :: Status -> H.ComponentHTML Action () m
renderStatus status =
  HH.div
    [ HP.classes $ statusClasses status ]
    [ HH.span [ HP.class_ (H.ClassName "status-icon") ]
        [ HH.text $ statusIcon status ]  -- "✓", "⚠", "✕"
    , HH.span [ HP.class_ (H.ClassName "status-text") ]
        [ HH.text $ statusLabel status ]  -- "Success", "Warning", "Error"
    ]

statusIcon :: Status -> String
statusIcon = case _ of
  Success -> "✓"
  Warning -> "⚠"
  Error -> "✕"
  Info -> "ℹ"
```

---

## Focus Indicators

### Visible Focus Ring

```css
/* Base focus style */
:focus {
  outline: none;
}

:focus-visible {
  outline: 2px solid var(--color-focus);
  outline-offset: 2px;
}

/* Button focus */
.btn:focus-visible {
  outline: 2px solid var(--color-focus);
  outline-offset: 2px;
  box-shadow: 0 0 0 4px var(--color-focus-ring);
}

/* Input focus */
.input:focus-visible {
  border-color: var(--color-focus);
  box-shadow: 0 0 0 3px var(--color-focus-ring);
}

/* List item focus */
.list-item:focus-visible {
  background: var(--color-bg-hover);
  outline: 2px solid var(--color-focus);
  outline-offset: -2px;
}

/* Skip link (hidden until focused) */
.skip-link {
  position: absolute;
  top: -100px;
  left: 50%;
  transform: translateX(-50%);
  padding: var(--space-2) var(--space-4);
  background: var(--color-bg-surface);
  border: 2px solid var(--color-focus);
  border-radius: 4px;
  z-index: 9999;
}

.skip-link:focus {
  top: var(--space-2);
}
```

---

## Reduced Motion

```css
/* Respect user's motion preferences */
@media (prefers-reduced-motion: reduce) {
  *,
  *::before,
  *::after {
    animation-duration: 0.01ms !important;
    animation-iteration-count: 1 !important;
    transition-duration: 0.01ms !important;
  }
  
  .toast {
    animation: none;
  }
  
  .loading-spinner {
    animation: none;
    /* Show static indicator instead */
  }
}
```

```purescript
-- Check motion preference in PureScript
foreign import prefersReducedMotion :: Effect Boolean

useAnimation :: Boolean -> String -> String
useAnimation reducedMotion animation =
  if reducedMotion then "none" else animation
```

---

## Form Accessibility

### Labels and Instructions

```purescript
renderInput :: InputConfig -> H.ComponentHTML Action () m
renderInput config =
  HH.div
    [ HP.class_ (H.ClassName "form-field") ]
    [ HH.label
        [ HP.for config.id
        , HP.class_ (H.ClassName "form-label")
        ]
        [ HH.text config.label
        , when config.required $
            HH.span
              [ HP.class_ (H.ClassName "required-indicator")
              , HP.attr (H.AttrName "aria-hidden") "true"
              ]
              [ HH.text " *" ]
        ]
    , case config.description of
        Just desc ->
          HH.p
            [ HP.id (config.id <> "-desc")
            , HP.class_ (H.ClassName "form-description")
            ]
            [ HH.text desc ]
        Nothing -> HH.text ""
    , HH.input
        [ HP.id config.id
        , HP.type_ config.inputType
        , HP.attr (H.AttrName "aria-describedby") $
            maybe "" (const (config.id <> "-desc")) config.description
        , HP.attr (H.AttrName "aria-required") $
            if config.required then "true" else "false"
        , HP.attr (H.AttrName "aria-invalid") $
            if isJust config.error then "true" else "false"
        ]
    , case config.error of
        Just err ->
          HH.p
            [ HP.id (config.id <> "-error")
            , HP.class_ (H.ClassName "form-error")
            , HP.attr (H.AttrName "role") "alert"
            ]
            [ HH.text err ]
        Nothing -> HH.text ""
    ]
```

### Error Handling

```purescript
-- Announce errors to screen readers
announceError :: String -> Effect Unit
announceError message = do
  let announcement = document.createElement "div"
  announcement.setAttribute "role" "alert"
  announcement.setAttribute "aria-live" "assertive"
  announcement.textContent = message
  document.body.appendChild announcement
  
  -- Remove after announcement
  setTimeout 1000 do
    document.body.removeChild announcement
```

---

## Component Patterns

### Modal Dialog

```purescript
renderModal :: ModalConfig -> H.ComponentHTML Action () m
renderModal config =
  HH.div
    [ HP.class_ (H.ClassName "modal-overlay")
    , HP.attr (H.AttrName "role") "dialog"
    , HP.attr (H.AttrName "aria-modal") "true"
    , HP.attr (H.AttrName "aria-labelledby") "modal-title"
    , HP.attr (H.AttrName "aria-describedby") "modal-desc"
    ]
    [ HH.div
        [ HP.class_ (H.ClassName "modal") ]
        [ HH.h2
            [ HP.id "modal-title" ]
            [ HH.text config.title ]
        , HH.p
            [ HP.id "modal-desc" ]
            [ HH.text config.description ]
        , HH.div [ HP.class_ (H.ClassName "modal-content") ]
            config.content
        , HH.div [ HP.class_ (H.ClassName "modal-actions") ]
            [ HH.button
                [ HP.attr (H.AttrName "autofocus") "true"
                , HE.onClick \_ -> config.onConfirm
                ]
                [ HH.text "Confirm" ]
            , HH.button
                [ HE.onClick \_ -> config.onCancel ]
                [ HH.text "Cancel" ]
            ]
        ]
    ]
```

### Tab Panel

```purescript
renderTabs :: Array Tab -> Int -> H.ComponentHTML Action () m
renderTabs tabs activeIndex =
  HH.div_
    [ HH.div
        [ HP.attr (H.AttrName "role") "tablist"
        , HP.attr (H.AttrName "aria-label") "Session views"
        ]
        (mapWithIndex renderTab tabs)
    , HH.div
        [ HP.attr (H.AttrName "role") "tabpanel"
        , HP.attr (H.AttrName "aria-labelledby") ("tab-" <> show activeIndex)
        , HP.id ("panel-" <> show activeIndex)
        ]
        [ (tabs !! activeIndex).content ]
    ]

renderTab :: Int -> Tab -> H.ComponentHTML Action () m
renderTab index tab =
  HH.button
    [ HP.attr (H.AttrName "role") "tab"
    , HP.attr (H.AttrName "aria-selected") (if index == activeIndex then "true" else "false")
    , HP.attr (H.AttrName "aria-controls") ("panel-" <> show index)
    , HP.id ("tab-" <> show index)
    , HP.tabIndex (if index == activeIndex then 0 else -1)
    ]
    [ HH.text tab.label ]
```

---

## Testing Accessibility

### Automated Testing

```typescript
// Using jest-axe
import { axe, toHaveNoViolations } from 'jest-axe';

expect.extend(toHaveNoViolations);

test('Dashboard has no accessibility violations', async () => {
  const { container } = render(<Dashboard />);
  const results = await axe(container);
  expect(results).toHaveNoViolations();
});
```

### Manual Testing Checklist

- [ ] Navigate entire app with keyboard only
- [ ] Test with screen reader (VoiceOver/NVDA)
- [ ] Verify focus order is logical
- [ ] Check color contrast with tools
- [ ] Test with 200% zoom
- [ ] Verify reduced motion preference
- [ ] Test with high contrast mode

---

## Related Specifications

- `48-KEYBOARD-NAVIGATION.md` - Full keyboard support
- `47-THEMING.md` - Color system
- `68-HELP-OVERLAY.md` - Keyboard shortcuts display

---

*"Accessibility is not a feature. It's a foundation."*
