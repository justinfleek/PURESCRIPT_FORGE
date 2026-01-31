# 69-QUICK-ACTIONS: Fast Access to Common Tasks

## Overview

The Quick Actions widget provides one-click access to frequently used operations, context-sensitive suggestions, and smart shortcuts based on current state.

---

## Visual Design

### Quick Actions Panel (Dashboard)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  QUICK ACTIONS                                                    [Edit ✎] │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ SUGGESTED ───────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  💡 Based on your current context:                                    │ │
│  │                                                                        │ │
│  │  ┌────────────────┐  ┌────────────────┐  ┌────────────────┐          │ │
│  │  │ 🔄 Continue    │  │ 📸 Snapshot    │  │ 🌿 Branch      │          │ │
│  │  │ Session        │  │ State          │  │ Session        │          │ │
│  │  └────────────────┘  └────────────────┘  └────────────────┘          │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ FAVORITES ───────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ┌────────────────┐  ┌────────────────┐  ┌────────────────┐          │ │
│  │  │ ➕ New         │  │ 📤 Export      │  │ 🔍 Search      │          │ │
│  │  │ Session        │  │ Session        │  │ History        │          │ │
│  │  │   Ctrl+N       │  │ Ctrl+Shift+E   │  │     /          │          │ │
│  │  └────────────────┘  └────────────────┘  └────────────────┘          │ │
│  │                                                                        │ │
│  │  ┌────────────────┐  ┌────────────────┐  ┌────────────────┐          │ │
│  │  │ ⏱ View        │  │ ⚙ Settings     │  │ 🎬 Start       │          │ │
│  │  │ Timeline       │  │                │  │ Recording      │          │ │
│  │  │     4          │  │     5          │  │                │          │ │
│  │  └────────────────┘  └────────────────┘  └────────────────┘          │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ RECENT ──────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  🕐 Continue "Debug Auth" session              5 min ago    [Open]    │ │
│  │  🕐 View exported markdown                     15 min ago   [Open]    │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Floating Quick Actions (Compact)

```
┌──────────────────────────────────────┐
│  ⚡                                  │
│  ┌────┐ ┌────┐ ┌────┐ ┌────┐ ┌────┐│
│  │ ➕ │ │ 📸 │ │ 🔍 │ │ 📤 │ │ ⋯  ││
│  └────┘ └────┘ └────┘ └────┘ └────┘│
└──────────────────────────────────────┘
```

### Edit Quick Actions

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  CUSTOMIZE QUICK ACTIONS                                             [✕]   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Drag to reorder. Click ★ to favorite.                                     │
│                                                                             │
│  ┌─ YOUR FAVORITES (max 6) ──────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ☰ ★ New Session                      ☰ ★ Export Session              │ │
│  │  ☰ ★ Search History                   ☰ ★ View Timeline               │ │
│  │  ☰ ★ Settings                         ☰ ★ Start Recording             │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ AVAILABLE ACTIONS ───────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ☆ Create Snapshot                    ☆ Branch Session                │ │
│  │  ☆ Compare Sessions                   ☆ Import Data                   │ │
│  │  ☆ Toggle Debug Mode                  ☆ Clear History                 │ │
│  │  ☆ Change Model                       ☆ View Performance              │ │
│  │  ☆ Keyboard Shortcuts                 ☆ Start Tour                    │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  [Reset to Defaults]                                         [Save]        │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Data Model

```typescript
interface QuickAction {
  id: string;
  label: string;
  icon: string;
  shortcut?: string;
  
  // Behavior
  action: () => void | Promise<void>;
  
  // Visibility
  when?: () => boolean;        // Show condition
  enabled?: () => boolean;     // Enabled condition
  
  // Categorization
  category: ActionCategory;
  isFavorite: boolean;
  usageCount: number;
  lastUsed?: Date;
}

type ActionCategory =
  | 'session'
  | 'navigation'
  | 'export'
  | 'snapshot'
  | 'settings'
  | 'tools';

interface QuickActionsState {
  favorites: string[];          // Action IDs
  recentActions: RecentAction[];
  suggestions: string[];        // Context-based suggestions
}

interface RecentAction {
  actionId: string;
  timestamp: Date;
  context?: string;             // What triggered it
}
```

---

## Available Actions

```typescript
const ALL_ACTIONS: QuickAction[] = [
  // Session
  {
    id: 'session.new',
    label: 'New Session',
    icon: '➕',
    shortcut: 'Ctrl+N',
    category: 'session',
    action: () => createNewSession()
  },
  {
    id: 'session.continue',
    label: 'Continue Session',
    icon: '🔄',
    category: 'session',
    action: () => continueLastSession(),
    when: () => hasRecentSession()
  },
  {
    id: 'session.branch',
    label: 'Branch Session',
    icon: '🌿',
    shortcut: 'gb',
    category: 'session',
    action: () => branchCurrentSession(),
    when: () => hasActiveSession()
  },
  
  // Snapshots
  {
    id: 'snapshot.create',
    label: 'Create Snapshot',
    icon: '📸',
    shortcut: 'Ctrl+S',
    category: 'snapshot',
    action: () => createSnapshot()
  },
  {
    id: 'snapshot.restore',
    label: 'Restore Snapshot',
    icon: '⏪',
    category: 'snapshot',
    action: () => openSnapshotPicker(),
    when: () => hasSnapshots()
  },
  
  // Navigation
  {
    id: 'nav.search',
    label: 'Search History',
    icon: '🔍',
    shortcut: '/',
    category: 'navigation',
    action: () => openSearch()
  },
  {
    id: 'nav.timeline',
    label: 'View Timeline',
    icon: '⏱',
    shortcut: '4',
    category: 'navigation',
    action: () => navigateTo(Timeline)
  },
  {
    id: 'nav.performance',
    label: 'View Performance',
    icon: '📊',
    category: 'navigation',
    action: () => navigateTo(Performance)
  },
  
  // Export/Import
  {
    id: 'export.session',
    label: 'Export Session',
    icon: '📤',
    shortcut: 'Ctrl+Shift+E',
    category: 'export',
    action: () => exportCurrentSession(),
    when: () => hasActiveSession()
  },
  {
    id: 'import.data',
    label: 'Import Data',
    icon: '📥',
    shortcut: 'Ctrl+I',
    category: 'export',
    action: () => openImportModal()
  },
  
  // Recording
  {
    id: 'recording.start',
    label: 'Start Recording',
    icon: '🎬',
    category: 'tools',
    action: () => startRecording(),
    when: () => !isRecording()
  },
  {
    id: 'recording.stop',
    label: 'Stop Recording',
    icon: '⏹',
    category: 'tools',
    action: () => stopRecording(),
    when: () => isRecording()
  },
  
  // Settings
  {
    id: 'settings.open',
    label: 'Settings',
    icon: '⚙',
    shortcut: '5',
    category: 'settings',
    action: () => navigateTo(Settings)
  },
  {
    id: 'settings.model',
    label: 'Change Model',
    icon: '🤖',
    category: 'settings',
    action: () => openModelPicker()
  },
  {
    id: 'settings.shortcuts',
    label: 'Keyboard Shortcuts',
    icon: '⌨',
    shortcut: '?',
    category: 'settings',
    action: () => showKeyboardShortcuts()
  },
  
  // Tools
  {
    id: 'tools.debug',
    label: 'Toggle Debug Mode',
    icon: '🔧',
    shortcut: 'Ctrl+Shift+D',
    category: 'tools',
    action: () => toggleDebugMode()
  },
  {
    id: 'tools.compare',
    label: 'Compare Sessions',
    icon: '⚖',
    category: 'tools',
    action: () => openSessionCompare()
  }
];
```

---

## Smart Suggestions

```typescript
// Generate context-aware suggestions
function getSuggestedActions(state: AppState): QuickAction[] {
  const suggestions: QuickAction[] = [];
  
  // If has active session with messages
  if (state.session?.messages.length > 0) {
    suggestions.push(findAction('snapshot.create'));
    
    if (!state.session.isRecording) {
      suggestions.push(findAction('recording.start'));
    }
  }
  
  // If session has branches
  if (state.session?.branchCount > 1) {
    suggestions.push(findAction('tools.compare'));
  }
  
  // If balance is low
  if (state.balance.diem < 10) {
    suggestions.push(findAction('settings.model'));  // Suggest smaller model
  }
  
  // If recent session exists
  if (state.recentSessions.length > 0 && !state.session) {
    suggestions.push(findAction('session.continue'));
  }
  
  // If has pending diffs
  if (state.pendingDiffs.length > 0) {
    suggestions.push(findAction('export.session'));
  }
  
  return suggestions.slice(0, 3);  // Max 3 suggestions
}
```

---

## PureScript Component

```purescript
module Sidepanel.Components.QuickActions where

type State =
  { favorites :: Array String
  , suggestions :: Array QuickAction
  , recentActions :: Array RecentAction
  , isEditing :: Boolean
  }

data Action
  = ExecuteAction String
  | ToggleFavorite String
  | ReorderFavorites (Array String)
  | OpenEditor
  | CloseEditor
  | SaveFavorites

render :: forall m. State -> AppState -> H.ComponentHTML Action () m
render state appState =
  HH.div
    [ HP.class_ (H.ClassName "quick-actions") ]
    [ renderHeader state.isEditing
    , when (not (null state.suggestions)) $
        renderSuggestions state.suggestions
    , renderFavorites state.favorites
    , when (not (null state.recentActions)) $
        renderRecent state.recentActions
    ]

renderFavorites :: forall m. Array String -> H.ComponentHTML Action () m
renderFavorites favoriteIds =
  HH.div
    [ HP.class_ (H.ClassName "quick-actions__favorites") ]
    [ HH.div [ HP.class_ (H.ClassName "quick-actions__label") ]
        [ HH.text "Favorites" ]
    , HH.div [ HP.class_ (H.ClassName "quick-actions__grid") ]
        (map renderActionCard (mapMaybe findAction favoriteIds))
    ]

renderActionCard :: forall m. QuickAction -> H.ComponentHTML Action () m
renderActionCard action =
  HH.button
    [ HP.classes $ actionCardClasses action
    , HP.disabled (not (fromMaybe true (action.enabled unit)))
    , HE.onClick \_ -> ExecuteAction action.id
    , HP.title $ maybe action.label (\s -> action.label <> " (" <> s <> ")") action.shortcut
    ]
    [ HH.span [ HP.class_ (H.ClassName "action-card__icon") ]
        [ HH.text action.icon ]
    , HH.span [ HP.class_ (H.ClassName "action-card__label") ]
        [ HH.text action.label ]
    , case action.shortcut of
        Just shortcut ->
          HH.span [ HP.class_ (H.ClassName "action-card__shortcut") ]
            [ HH.text shortcut ]
        Nothing -> HH.text ""
    ]
```

---

## CSS Styling

```css
.quick-actions {
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: 8px;
  overflow: hidden;
}

.quick-actions__header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: var(--space-3);
  border-bottom: 1px solid var(--color-border-subtle);
}

.quick-actions__label {
  font-size: var(--font-size-xs);
  font-weight: var(--font-weight-semibold);
  color: var(--color-text-tertiary);
  text-transform: uppercase;
  letter-spacing: var(--letter-spacing-wider);
  margin-bottom: var(--space-2);
}

.quick-actions__grid {
  display: grid;
  grid-template-columns: repeat(3, 1fr);
  gap: var(--space-2);
  padding: var(--space-3);
}

.action-card {
  display: flex;
  flex-direction: column;
  align-items: center;
  gap: var(--space-1);
  padding: var(--space-3);
  background: var(--color-bg-base);
  border: 1px solid var(--color-border-subtle);
  border-radius: 8px;
  cursor: pointer;
  transition: all var(--transition-fast);
}

.action-card:hover {
  background: var(--color-bg-hover);
  border-color: var(--color-primary-dim);
}

.action-card:active {
  transform: scale(0.98);
}

.action-card--disabled {
  opacity: 0.5;
  cursor: not-allowed;
}

.action-card__icon {
  font-size: 24px;
}

.action-card__label {
  font-size: var(--font-size-xs);
  color: var(--color-text-secondary);
  text-align: center;
}

.action-card__shortcut {
  font-size: 10px;
  font-family: var(--font-mono);
  color: var(--color-text-tertiary);
  padding: 1px 4px;
  background: var(--color-bg-elevated);
  border-radius: 2px;
}

/* Suggestions section */
.quick-actions__suggestions {
  padding: var(--space-3);
  background: var(--color-primary-dim);
  border-bottom: 1px solid var(--color-border-subtle);
}

.quick-actions__suggestions .action-card {
  background: var(--color-bg-surface);
}

/* Recent section */
.quick-actions__recent {
  padding: var(--space-3);
  border-top: 1px solid var(--color-border-subtle);
}

.recent-item {
  display: flex;
  align-items: center;
  gap: var(--space-2);
  padding: var(--space-2);
  font-size: var(--font-size-sm);
  color: var(--color-text-secondary);
}

.recent-item__time {
  color: var(--color-text-tertiary);
  font-size: var(--font-size-xs);
}
```

---

## Related Specifications

- `46-COMMAND-PALETTE.md` - All commands
- `50-DASHBOARD-LAYOUT.md` - Widget placement
- `48-KEYBOARD-NAVIGATION.md` - Shortcuts

---

*"One click. Zero friction."*
