# 61-PROOF-PANEL: Lean4 Proof Status Display

## Overview

The Proof Panel displays Lean4 theorem prover state, showing proof goals, diagnostics, and tactic suggestions. This is a key differentiator for our formal methods-oriented target users.

**Phase:** 3 (Advanced Features)

---

## Why Proof Integration?

Our target audience includes senior engineers who value:
1. **Correctness guarantees** - "Prove it, don't just test it"
2. **Interactive theorem proving** - Real-time feedback on proof state
3. **Tactic suggestions** - AI-powered proof assistance

The sidepanel brings proof state visibility outside the editor.

---

## Visual Design

### Proof Panel Layout

```
┌─────────────────────────────────────────────────────────────────────────┐
│  PROOF STATUS                                         ● Connected (Lean)│
├─────────────────────────────────────────────────────────────────────────┤
│                                                                          │
│  Current File: Sidepanel/Theorems/Balance.lean                          │
│                                                                          │
│  GOALS (2)                                                               │
│  ────────────────────────────────────────────────────────────────────   │
│                                                                          │
│  ┌───────────────────────────────────────────────────────────────────┐  │
│  │  Goal 1                                                            │  │
│  │                                                                    │  │
│  │  ⊢ ∀ (b₁ b₂ : Balance),                                           │  │
│  │      b₁.diem ≤ b₂.diem →                                          │  │
│  │      b₁.effective ≤ b₂.effective                                  │  │
│  │                                                                    │  │
│  │  Context:                                                          │  │
│  │    b₁ : Balance                                                   │  │
│  │    b₂ : Balance                                                   │  │
│  │    h : b₁.diem ≤ b₂.diem                                         │  │
│  └───────────────────────────────────────────────────────────────────┘  │
│                                                                          │
│  ┌───────────────────────────────────────────────────────────────────┐  │
│  │  Goal 2                                                            │  │
│  │                                                                    │  │
│  │  ⊢ b₁.usd = b₂.usd                                                │  │
│  └───────────────────────────────────────────────────────────────────┘  │
│                                                                          │
│  DIAGNOSTICS                                                             │
│  ────────────────────────────────────────────────────────────────────   │
│  ⚠ Line 42: unused variable 'h'                                         │
│                                                                          │
│  SUGGESTED TACTICS                                                       │
│  ────────────────────────────────────────────────────────────────────   │
│  • intro h                    Apply intro to bind hypothesis             │
│  • apply le_trans             Use transitivity of ≤                     │
│  • simp [Balance.effective]   Simplify with definition                  │
│                                                                          │
└─────────────────────────────────────────────────────────────────────────┘
```

---

## Data Flow

### From Lean LSP via MCP

```
Lean4 File    →    lean-lsp-mcp    →    Bridge    →    Browser
   │                    │                  │              │
   │ (edit)             │                  │              │
   └────────────────────┤                  │              │
                        │ goal_state       │              │
                        │ diagnostics      │              │
                        └──────────────────┤              │
                                           │ proof.update │
                                           └──────────────┤
                                                          │ render
```

### MCP Tools Used

```typescript
// Tools provided by lean-lsp-mcp
interface LeanMCPTools {
  // Get current proof goals at cursor
  lean_goal: (params: { file: string; line: number; column: number }) => GoalState;
  
  // Get diagnostics for file
  lean_diagnostic_messages: (params: { file: string }) => Diagnostic[];
  
  // Get completions (tactics, theorems)
  lean_completions: (params: { file: string; line: number; column: number }) => Completion[];
  
  // Search theorem library
  lean_search: (params: { query: string; maxResults?: number }) => SearchResult[];
}
```

---

## PureScript Implementation

### Types

```purescript
module Sidepanel.Components.Proof.ProofPanel where

import Prelude
import Data.Array (Array)
import Data.Maybe (Maybe)

-- Proof goal from Lean
type ProofGoal =
  { index :: Int
  , type_ :: String       -- The goal to prove
  , context :: Array ContextItem
  }

type ContextItem =
  { name :: String
  , type_ :: String
  , value :: Maybe String  -- For let-bindings
  }

-- Diagnostic message
type Diagnostic =
  { severity :: DiagnosticSeverity
  , line :: Int
  , column :: Int
  , message :: String
  }

data DiagnosticSeverity = Error | Warning | Info | Hint

-- Tactic suggestion
type TacticSuggestion =
  { tactic :: String
  , description :: String
  , confidence :: Number  -- 0-1
  }

-- Component state
type State =
  { connected :: Boolean
  , currentFile :: Maybe String
  , goals :: Array ProofGoal
  , diagnostics :: Array Diagnostic
  , suggestions :: Array TacticSuggestion
  , expandedGoals :: Set Int
  , isLoadingSuggestions :: Boolean
  }

-- Actions
data Action
  = Initialize
  | Receive ProofState
  | ToggleGoalExpand Int
  | ApplyTactic String
  | RefreshGoals
  | SearchTheorems String

-- Input from parent
type Input = ProofState

type ProofState =
  { connected :: Boolean
  , currentFile :: Maybe String
  , goals :: Array ProofGoal
  , diagnostics :: Array Diagnostic
  , suggestions :: Array TacticSuggestion
  }
```

### Component

```purescript
component :: forall q o m. MonadAff m => H.Component q Input o m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { connected: input.connected
  , currentFile: input.currentFile
  , goals: input.goals
  , diagnostics: input.diagnostics
  , suggestions: input.suggestions
  , expandedGoals: Set.singleton 0  -- First goal expanded by default
  , isLoadingSuggestions: false
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "proof-panel") ]
    [ renderHeader state
    , renderCurrentFile state.currentFile
    , renderGoals state
    , renderDiagnostics state.diagnostics
    , renderSuggestions state
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.header
    [ HP.class_ (H.ClassName "proof-panel__header") ]
    [ HH.h2_ [ HH.text "Proof Status" ]
    , HH.div
        [ HP.classes $ connectionClasses state.connected ]
        [ HH.span [ HP.class_ (H.ClassName "connection-dot") ] []
        , HH.text $ if state.connected then "Connected (Lean)" else "Disconnected"
        ]
    ]

renderCurrentFile :: forall m. Maybe String -> H.ComponentHTML Action () m
renderCurrentFile = case _ of
  Nothing ->
    HH.div
      [ HP.class_ (H.ClassName "proof-panel__file proof-panel__file--none") ]
      [ HH.text "No Lean file open" ]
  Just file ->
    HH.div
      [ HP.class_ (H.ClassName "proof-panel__file") ]
      [ HH.text $ "Current File: " <> file ]

renderGoals :: forall m. State -> H.ComponentHTML Action () m
renderGoals state =
  HH.section
    [ HP.class_ (H.ClassName "proof-panel__goals") ]
    [ HH.div
        [ HP.class_ (H.ClassName "section-header") ]
        [ HH.text $ "Goals (" <> show (length state.goals) <> ")" ]
    , if null state.goals
        then HH.div
          [ HP.class_ (H.ClassName "goals-empty") ]
          [ HH.text "✓ No goals - proof complete!" ]
        else HH.div
          [ HP.class_ (H.ClassName "goals-list") ]
          (mapWithIndex (renderGoal state.expandedGoals) state.goals)
    ]

renderGoal :: forall m. Set Int -> Int -> ProofGoal -> H.ComponentHTML Action () m
renderGoal expandedSet index goal =
  let isExpanded = Set.member index expandedSet
  in
    HH.div
      [ HP.classes [ H.ClassName "goal-card", if isExpanded then H.ClassName "goal-card--expanded" else H.ClassName "" ]
      , HE.onClick \_ -> ToggleGoalExpand index
      ]
      [ HH.div
          [ HP.class_ (H.ClassName "goal-card__header") ]
          [ HH.span [ HP.class_ (H.ClassName "goal-card__title") ]
              [ HH.text $ "Goal " <> show (index + 1) ]
          , HH.span [ HP.class_ (H.ClassName "goal-card__expand") ]
              [ HH.text $ if isExpanded then "▼" else "▶" ]
          ]
      , HH.div
          [ HP.class_ (H.ClassName "goal-card__type") ]
          [ HH.code_ [ HH.text $ "⊢ " <> goal.type_ ] ]
      , when isExpanded $
          HH.div
            [ HP.class_ (H.ClassName "goal-card__context") ]
            [ HH.div [ HP.class_ (H.ClassName "context-title") ] [ HH.text "Context:" ]
            , HH.div
                [ HP.class_ (H.ClassName "context-items") ]
                (map renderContextItem goal.context)
            ]
      ]

renderContextItem :: forall m. ContextItem -> H.ComponentHTML Action () m
renderContextItem { name, type_, value } =
  HH.div
    [ HP.class_ (H.ClassName "context-item") ]
    [ HH.code_
        [ HH.span [ HP.class_ (H.ClassName "context-name") ] [ HH.text name ]
        , HH.text " : "
        , HH.span [ HP.class_ (H.ClassName "context-type") ] [ HH.text type_ ]
        , case value of
            Just v -> HH.span_ [ HH.text $ " := " <> v ]
            Nothing -> HH.text ""
        ]
    ]

renderDiagnostics :: forall m. Array Diagnostic -> H.ComponentHTML Action () m
renderDiagnostics diagnostics =
  when (not $ null diagnostics) $
    HH.section
      [ HP.class_ (H.ClassName "proof-panel__diagnostics") ]
      [ HH.div [ HP.class_ (H.ClassName "section-header") ] [ HH.text "Diagnostics" ]
      , HH.div
          [ HP.class_ (H.ClassName "diagnostics-list") ]
          (map renderDiagnostic diagnostics)
      ]

renderDiagnostic :: forall m. Diagnostic -> H.ComponentHTML Action () m
renderDiagnostic diag =
  HH.div
    [ HP.classes $ diagnosticClasses diag.severity ]
    [ HH.span [ HP.class_ (H.ClassName "diagnostic-icon") ]
        [ HH.text $ severityIcon diag.severity ]
    , HH.span [ HP.class_ (H.ClassName "diagnostic-location") ]
        [ HH.text $ "Line " <> show diag.line <> ": " ]
    , HH.span [ HP.class_ (H.ClassName "diagnostic-message") ]
        [ HH.text diag.message ]
    ]

severityIcon :: DiagnosticSeverity -> String
severityIcon = case _ of
  Error -> "✗"
  Warning -> "⚠"
  Info -> "ℹ"
  Hint -> "💡"

renderSuggestions :: forall m. State -> H.ComponentHTML Action () m
renderSuggestions state =
  HH.section
    [ HP.class_ (H.ClassName "proof-panel__suggestions") ]
    [ HH.div [ HP.class_ (H.ClassName "section-header") ] [ HH.text "Suggested Tactics" ]
    , if state.isLoadingSuggestions
        then HH.div [ HP.class_ (H.ClassName "suggestions-loading") ] 
          [ HH.text "Analyzing..." ]
        else if null state.suggestions
          then HH.div [ HP.class_ (H.ClassName "suggestions-empty") ]
            [ HH.text "No suggestions available" ]
          else HH.div
            [ HP.class_ (H.ClassName "suggestions-list") ]
            (map renderSuggestion state.suggestions)
    ]

renderSuggestion :: forall m. TacticSuggestion -> H.ComponentHTML Action () m
renderSuggestion { tactic, description } =
  HH.div
    [ HP.class_ (H.ClassName "suggestion-item")
    , HE.onClick \_ -> ApplyTactic tactic
    ]
    [ HH.code [ HP.class_ (H.ClassName "suggestion-tactic") ] [ HH.text tactic ]
    , HH.span [ HP.class_ (H.ClassName "suggestion-description") ] [ HH.text description ]
    ]
```

---

## CSS Styling

```css
.proof-panel {
  display: flex;
  flex-direction: column;
  height: 100%;
  overflow-y: auto;
}

.proof-panel__header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  padding: var(--space-4);
  border-bottom: 1px solid var(--color-border-subtle);
}

.proof-panel__file {
  padding: var(--space-2) var(--space-4);
  background: var(--color-bg-surface);
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  color: var(--color-text-secondary);
}

.proof-panel__file--none {
  color: var(--color-text-tertiary);
  font-style: italic;
}

.section-header {
  font-family: var(--font-mono);
  font-size: var(--font-size-xs);
  font-weight: var(--font-weight-semibold);
  color: var(--color-text-secondary);
  text-transform: uppercase;
  letter-spacing: var(--letter-spacing-wider);
  padding: var(--space-3) var(--space-4);
}

.goals-list {
  padding: 0 var(--space-4) var(--space-4);
  display: flex;
  flex-direction: column;
  gap: var(--space-2);
}

.goals-empty {
  padding: var(--space-4);
  text-align: center;
  color: var(--color-success);
  font-family: var(--font-mono);
}

.goal-card {
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: 8px;
  padding: var(--space-3);
  cursor: pointer;
  transition: border-color var(--transition-fast);
}

.goal-card:hover {
  border-color: var(--color-border-default);
}

.goal-card__header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  margin-bottom: var(--space-2);
}

.goal-card__title {
  font-size: var(--font-size-sm);
  font-weight: var(--font-weight-medium);
  color: var(--color-text-primary);
}

.goal-card__expand {
  color: var(--color-text-tertiary);
  font-size: var(--font-size-xs);
}

.goal-card__type {
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  color: var(--color-primary);
  background: var(--color-bg-base);
  padding: var(--space-2);
  border-radius: 4px;
  overflow-x: auto;
}

.goal-card__context {
  margin-top: var(--space-3);
  padding-top: var(--space-3);
  border-top: 1px solid var(--color-border-subtle);
}

.context-title {
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
  margin-bottom: var(--space-2);
}

.context-item {
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  padding: var(--space-1) 0;
}

.context-name {
  color: var(--color-info);
}

.context-type {
  color: var(--color-text-secondary);
}

.diagnostics-list {
  padding: 0 var(--space-4) var(--space-4);
}

.diagnostic-item {
  display: flex;
  align-items: flex-start;
  gap: var(--space-2);
  padding: var(--space-2);
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
}

.diagnostic-item--error {
  color: var(--color-error);
}

.diagnostic-item--warning {
  color: var(--color-warning);
}

.diagnostic-location {
  color: var(--color-text-tertiary);
}

.suggestions-list {
  padding: 0 var(--space-4) var(--space-4);
  display: flex;
  flex-direction: column;
  gap: var(--space-2);
}

.suggestion-item {
  display: flex;
  align-items: center;
  gap: var(--space-3);
  padding: var(--space-2);
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: 6px;
  cursor: pointer;
  transition: all var(--transition-fast);
}

.suggestion-item:hover {
  border-color: var(--color-primary);
  background: var(--color-primary-dim);
}

.suggestion-tactic {
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  color: var(--color-primary);
  white-space: nowrap;
}

.suggestion-description {
  font-size: var(--font-size-sm);
  color: var(--color-text-secondary);
}
```

---

## Related Specifications

- `27-MCP-CONFIGURATION.md` - lean-lsp-mcp setup
- `62-TACTIC-SUGGESTIONS.md` - Tactic suggestion algorithm
- `89-IMPLEMENTATION-ROADMAP.md` - Phase 3 timeline

---

*"In proof we trust."*
