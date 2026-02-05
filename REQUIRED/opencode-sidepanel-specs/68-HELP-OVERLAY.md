# 68-HELP-OVERLAY: Onboarding and Reference System

## Overview

The Help Overlay provides in-app guidance including keyboard shortcut reference, feature tours, contextual help, and onboarding for new users.

---

## Components

1. **Keyboard Shortcut Reference** - Quick reference modal (?)
2. **Feature Tour** - First-time user onboarding
3. **Contextual Help** - Help buttons throughout UI
4. **Command Palette Help** - Integrated into Ctrl+Shift+P
5. **Tooltips** - Hover hints on controls

---

## Visual Design

### Keyboard Shortcut Reference (?  or Ctrl+/)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  KEYBOARD SHORTCUTS                                                    [✕]  │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ NAVIGATION ──────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  1 / g d          Go to Dashboard                                     │ │
│  │  2 / g s          Go to Session                                       │ │
│  │  3 / g p          Go to Proofs                                        │ │
│  │  4 / g t          Go to Timeline                                      │ │
│  │  5 / g e          Go to Settings                                      │ │
│  │  g f              Go to Files                                         │ │
│  │  g r              Go to Recordings                                    │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ MOVEMENT ────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  j / ↓            Move down                                           │ │
│  │  k / ↑            Move up                                             │ │
│  │  h / ←            Move left / Collapse                                │ │
│  │  l / →            Move right / Expand                                 │ │
│  │  gg               Go to first item                                    │ │
│  │  G                Go to last item                                     │ │
│  │  Ctrl+d           Page down                                           │ │
│  │  Ctrl+u           Page up                                             │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ ACTIONS ─────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  Enter            Select / Open                                       │ │
│  │  Escape           Close / Cancel / Back                               │ │
│  │  /                Open search                                         │ │
│  │  Ctrl+Shift+P     Command palette                                     │ │
│  │  ?                Show this help                                      │ │
│  │  r                Refresh current view                                │ │
│  │  [                Toggle sidebar collapsed                            │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ DASHBOARD ───────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  g b              Focus balance widget                                │ │
│  │  g c              Focus countdown widget                              │ │
│  │  g u              Focus usage chart                                   │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ PROOFS ──────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  Tab              Next goal                                           │ │
│  │  Shift+Tab        Previous goal                                       │ │
│  │  a                Apply selected tactic                               │ │
│  │  p                Preview selected tactic                             │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  Press ? to toggle this help • Esc to close                               │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Feature Tour (First Launch)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│                          ◉ WELCOME TO OPENCODE SIDEPANEL                   │
│                                                                             │
│                     Your AI Coding Command Center                          │
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐  │
│  │                                                                       │  │
│  │                        [Dashboard Screenshot]                        │  │
│  │                                                                       │  │
│  └─────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  The sidepanel gives you complete visibility into your AI coding          │
│  sessions: track your Diem balance, analyze token usage, verify proofs,   │
│  and time-travel through your conversation history.                       │
│                                                                             │
│                                                                             │
│                              ○ ● ○ ○ ○                                    │
│                                                                             │
│                                                                             │
│  [Skip Tour]                                              [Next: Balance →] │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Tour Step 2 - Diem Balance

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│                          TRACK YOUR DIEM BALANCE                           │
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐  │
│  │  ┌──────────────────────────────────────────┐                       │  │
│  │  │  ◉ DIEM BALANCE                          │ ← Your daily credit   │  │
│  │  │      42.5                                │                       │  │
│  │  │  ██████████████████░░░░░░░░░░            │ ← Usage bar           │  │
│  │  │                                          │                       │  │
│  │  │  5.2/hr    ~8h left    4h 23m           │ ← Smart predictions   │  │
│  │  │  burn rate            until reset        │                       │  │
│  │  └──────────────────────────────────────────┘                       │  │
│  └─────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  Venice gives you free daily credits (Diem) that reset at midnight UTC.   │
│  The sidepanel tracks your balance in real-time and predicts when         │
│  you'll run out based on your current usage rate.                         │
│                                                                             │
│                              ○ ○ ● ○ ○                                    │
│                                                                             │
│  [← Back]                                    [Next: Keyboard Shortcuts →]  │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Contextual Help Popover

```
┌────────────────────────────────────────────────┐
│                                                │
│  📊 Token Usage Chart                          │
│                                                │
│  This chart shows your token consumption      │
│  over time. Prompt tokens (input) are shown   │
│  in purple, completion tokens (output) in     │
│  green.                                       │
│                                                │
│  Tips:                                        │
│  • Hover over points for exact values        │
│  • Click time ranges to zoom in/out          │
│  • Large spikes often indicate file reads    │
│                                                │
│  [Learn More]              [Got it, thanks!] │
└────────────────────────────────────────────────┘
```

---

## Data Model

```typescript
interface HelpContent {
  shortcuts: ShortcutCategory[];
  tourSteps: TourStep[];
  contextualHelp: Map<string, ContextualHelpItem>;
}

interface ShortcutCategory {
  name: string;
  shortcuts: Shortcut[];
}

interface Shortcut {
  keys: string[];  // e.g., ["g", "d"] or ["Ctrl", "Shift", "P"]
  description: string;
  context?: string;  // When applicable (e.g., "in Proofs view")
}

interface TourStep {
  id: string;
  title: string;
  content: string;
  image?: string;
  targetElement?: string;  // CSS selector for highlighting
  position?: 'top' | 'bottom' | 'left' | 'right';
}

interface ContextualHelpItem {
  id: string;
  title: string;
  content: string;
  tips?: string[];
  learnMoreUrl?: string;
}

interface HelpState {
  isShortcutsOpen: boolean;
  isTourActive: boolean;
  currentTourStep: number;
  dismissedHelp: Set<string>;
  hasCompletedTour: boolean;
}
```

---

## PureScript Implementation

```purescript
module Sidepanel.Components.Help where

import Prelude
import Data.Array (Array)
import Data.Set (Set)
import Data.Map (Map)
import Data.Maybe (Maybe)

type ShortcutCategory =
  { name :: String
  , shortcuts :: Array Shortcut
  }

type Shortcut =
  { keys :: Array String
  , description :: String
  , context :: Maybe String
  }

type TourStep =
  { id :: String
  , title :: String
  , content :: String
  , image :: Maybe String
  }

type State =
  { isShortcutsOpen :: Boolean
  , isTourActive :: Boolean
  , currentTourStep :: Int
  , hasCompletedTour :: Boolean
  }

data Action
  = ToggleShortcuts
  | CloseShortcuts
  | StartTour
  | NextTourStep
  | PreviousTourStep
  | SkipTour
  | CompleteTour
  | ShowContextualHelp String
  | DismissContextualHelp String

-- Shortcut data
allShortcuts :: Array ShortcutCategory
allShortcuts =
  [ { name: "Navigation"
    , shortcuts:
        [ { keys: ["1"], description: "Go to Dashboard", context: Nothing }
        , { keys: ["2"], description: "Go to Session", context: Nothing }
        , { keys: ["3"], description: "Go to Proofs", context: Nothing }
        , { keys: ["4"], description: "Go to Timeline", context: Nothing }
        , { keys: ["5"], description: "Go to Settings", context: Nothing }
        , { keys: ["g", "d"], description: "Go to Dashboard", context: Nothing }
        , { keys: ["g", "s"], description: "Go to Session", context: Nothing }
        , { keys: ["g", "p"], description: "Go to Proofs", context: Nothing }
        , { keys: ["g", "t"], description: "Go to Timeline", context: Nothing }
        , { keys: ["g", "f"], description: "Go to Files", context: Nothing }
        , { keys: ["g", "r"], description: "Go to Recordings", context: Nothing }
        ]
    }
  , { name: "Movement"
    , shortcuts:
        [ { keys: ["j"], description: "Move down", context: Nothing }
        , { keys: ["k"], description: "Move up", context: Nothing }
        , { keys: ["h"], description: "Move left / Collapse", context: Nothing }
        , { keys: ["l"], description: "Move right / Expand", context: Nothing }
        , { keys: ["g", "g"], description: "Go to first item", context: Nothing }
        , { keys: ["G"], description: "Go to last item", context: Nothing }
        , { keys: ["Ctrl", "d"], description: "Page down", context: Nothing }
        , { keys: ["Ctrl", "u"], description: "Page up", context: Nothing }
        ]
    }
  , { name: "Actions"
    , shortcuts:
        [ { keys: ["Enter"], description: "Select / Open", context: Nothing }
        , { keys: ["Escape"], description: "Close / Cancel / Back", context: Nothing }
        , { keys: ["/"], description: "Open search", context: Nothing }
        , { keys: ["Ctrl", "Shift", "P"], description: "Command palette", context: Nothing }
        , { keys: ["?"], description: "Show keyboard shortcuts", context: Nothing }
        , { keys: ["r"], description: "Refresh current view", context: Nothing }
        , { keys: ["["], description: "Toggle sidebar", context: Nothing }
        ]
    }
  , { name: "Proofs"
    , shortcuts:
        [ { keys: ["Tab"], description: "Next goal", context: Just "in Proofs view" }
        , { keys: ["Shift", "Tab"], description: "Previous goal", context: Just "in Proofs view" }
        , { keys: ["a"], description: "Apply selected tactic", context: Just "in Proofs view" }
        , { keys: ["p"], description: "Preview selected tactic", context: Just "in Proofs view" }
        ]
    }
  ]

-- Tour steps
tourSteps :: Array TourStep
tourSteps =
  [ { id: "welcome"
    , title: "Welcome to OpenCode Sidepanel"
    , content: "Your AI Coding Command Center. The sidepanel gives you complete visibility into your AI coding sessions."
    , image: Just "/images/tour/welcome.png"
    }
  , { id: "balance"
    , title: "Track Your Diem Balance"
    , content: "Venice gives you free daily credits (Diem) that reset at midnight UTC. Watch your balance in real-time and see predictions for when you'll run out."
    , image: Just "/images/tour/balance.png"
    }
  , { id: "shortcuts"
    , title: "Keyboard-First Design"
    , content: "Navigate with Vim-style keys (j/k/h/l), jump to views with number keys (1-5), and access everything from the command palette (Ctrl+Shift+P)."
    , image: Nothing
    }
  , { id: "sessions"
    , title: "Session Intelligence"
    , content: "See token usage per message, track tool executions, and branch conversations to try different approaches."
    , image: Just "/images/tour/sessions.png"
    }
  , { id: "proofs"
    , title: "Formal Verification"
    , content: "Integrate Lean4 proofs into your workflow. See proof goals, get AI-powered tactic suggestions, and verify correctness."
    , image: Just "/images/tour/proofs.png"
    }
  ]

-- Component
component :: forall q o m. MonadAff m => H.Component q Unit o m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval { handleAction = handleAction }
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div_
    [ -- Shortcuts modal
      when state.isShortcutsOpen renderShortcutsModal
    
    -- Tour overlay
    , when state.isTourActive (renderTourStep state.currentTourStep)
    ]

renderShortcutsModal :: forall m. H.ComponentHTML Action () m
renderShortcutsModal =
  HH.div
    [ HP.class_ (H.ClassName "help-modal-overlay")
    , HE.onClick \_ -> CloseShortcuts
    ]
    [ HH.div
        [ HP.class_ (H.ClassName "help-modal")
        , HE.onClick (const Nothing)  -- Prevent propagation
        ]
        [ HH.div
            [ HP.class_ (H.ClassName "help-modal__header") ]
            [ HH.text "Keyboard Shortcuts"
            , HH.button
                [ HP.class_ (H.ClassName "help-modal__close")
                , HE.onClick \_ -> CloseShortcuts
                ]
                [ HH.text "✕" ]
            ]
        , HH.div
            [ HP.class_ (H.ClassName "help-modal__content") ]
            (map renderShortcutCategory allShortcuts)
        , HH.div
            [ HP.class_ (H.ClassName "help-modal__footer") ]
            [ HH.text "Press ? to toggle this help • Esc to close" ]
        ]
    ]

renderShortcutCategory :: forall m. ShortcutCategory -> H.ComponentHTML Action () m
renderShortcutCategory category =
  HH.div
    [ HP.class_ (H.ClassName "shortcut-category") ]
    [ HH.div
        [ HP.class_ (H.ClassName "shortcut-category__title") ]
        [ HH.text category.name ]
    , HH.div
        [ HP.class_ (H.ClassName "shortcut-category__list") ]
        (map renderShortcut category.shortcuts)
    ]

renderShortcut :: forall m. Shortcut -> H.ComponentHTML Action () m
renderShortcut shortcut =
  HH.div
    [ HP.class_ (H.ClassName "shortcut") ]
    [ HH.div
        [ HP.class_ (H.ClassName "shortcut__keys") ]
        (map renderKey shortcut.keys)
    , HH.div
        [ HP.class_ (H.ClassName "shortcut__description") ]
        [ HH.text shortcut.description ]
    ]

renderKey :: forall m. String -> H.ComponentHTML Action () m
renderKey key =
  HH.kbd
    [ HP.class_ (H.ClassName "key") ]
    [ HH.text key ]
```

---

## CSS Styling

```css
.help-modal-overlay {
  position: fixed;
  inset: 0;
  background: rgba(0, 0, 0, 0.7);
  display: flex;
  align-items: center;
  justify-content: center;
  z-index: 1000;
  animation: fadeIn 0.15s ease-out;
}

.help-modal {
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-default);
  border-radius: 12px;
  max-width: 600px;
  max-height: 80vh;
  overflow: hidden;
  display: flex;
  flex-direction: column;
  animation: slideUp 0.2s ease-out;
}

@keyframes slideUp {
  from {
    opacity: 0;
    transform: translateY(20px);
  }
  to {
    opacity: 1;
    transform: translateY(0);
  }
}

.help-modal__header {
  display: flex;
  align-items: center;
  justify-content: space-between;
  padding: var(--space-4);
  border-bottom: 1px solid var(--color-border-subtle);
  font-weight: var(--font-weight-semibold);
}

.help-modal__close {
  background: none;
  border: none;
  color: var(--color-text-tertiary);
  cursor: pointer;
  font-size: 18px;
}

.help-modal__content {
  flex: 1;
  overflow-y: auto;
  padding: var(--space-4);
}

.help-modal__footer {
  padding: var(--space-3);
  text-align: center;
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
  border-top: 1px solid var(--color-border-subtle);
}

.shortcut-category {
  margin-bottom: var(--space-4);
}

.shortcut-category__title {
  font-size: var(--font-size-sm);
  font-weight: var(--font-weight-semibold);
  color: var(--color-text-secondary);
  text-transform: uppercase;
  letter-spacing: var(--letter-spacing-wider);
  margin-bottom: var(--space-2);
  padding-bottom: var(--space-1);
  border-bottom: 1px solid var(--color-border-subtle);
}

.shortcut-category__list {
  display: flex;
  flex-direction: column;
  gap: var(--space-1);
}

.shortcut {
  display: flex;
  align-items: center;
  gap: var(--space-3);
  padding: var(--space-1) 0;
}

.shortcut__keys {
  display: flex;
  gap: var(--space-1);
  min-width: 120px;
}

.key {
  display: inline-block;
  padding: 2px 6px;
  background: var(--color-bg-base);
  border: 1px solid var(--color-border-subtle);
  border-radius: 4px;
  font-family: var(--font-mono);
  font-size: var(--font-size-xs);
  color: var(--color-text-secondary);
}

.shortcut__description {
  font-size: var(--font-size-sm);
  color: var(--color-text-primary);
}

/* Tour overlay */
.tour-overlay {
  position: fixed;
  inset: 0;
  background: rgba(0, 0, 0, 0.85);
  z-index: 1001;
}

.tour-spotlight {
  position: absolute;
  box-shadow: 0 0 0 9999px rgba(0, 0, 0, 0.85);
  border-radius: 8px;
  z-index: 1002;
}

.tour-card {
  position: absolute;
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-default);
  border-radius: 12px;
  padding: var(--space-5);
  max-width: 400px;
  z-index: 1003;
}

.tour-card__title {
  font-size: var(--font-size-lg);
  font-weight: var(--font-weight-bold);
  margin-bottom: var(--space-3);
}

.tour-card__content {
  font-size: var(--font-size-sm);
  color: var(--color-text-secondary);
  line-height: 1.6;
  margin-bottom: var(--space-4);
}

.tour-card__image {
  width: 100%;
  border-radius: 8px;
  margin-bottom: var(--space-4);
}

.tour-card__progress {
  display: flex;
  justify-content: center;
  gap: var(--space-1);
  margin-bottom: var(--space-4);
}

.tour-card__dot {
  width: 8px;
  height: 8px;
  border-radius: 50%;
  background: var(--color-bg-base);
}

.tour-card__dot--active {
  background: var(--color-primary);
}

.tour-card__actions {
  display: flex;
  justify-content: space-between;
}
```

---

## Persistence

```typescript
// Save tour completion
localStorage.setItem('sidepanel.tour.completed', 'true');

// Save dismissed contextual help
const dismissed = JSON.parse(localStorage.getItem('sidepanel.help.dismissed') || '[]');
dismissed.push(helpId);
localStorage.setItem('sidepanel.help.dismissed', JSON.stringify(dismissed));
```

---

## Related Specifications

- `48-KEYBOARD-NAVIGATION.md` - Keyboard system
- `55-SETTINGS-PANEL.md` - Settings for help preferences
- `85-CODE-STYLE-GUIDE.md` - Documentation standards

---

*"Great software teaches itself. The best help is the help you don't need."*
