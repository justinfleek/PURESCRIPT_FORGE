# 62-TACTIC-SUGGESTIONS: AI-Powered Proof Assistance

## Overview

The Tactic Suggestions system uses the AI model to analyze Lean4 proof goals and suggest appropriate tactics. It combines LSP information with AI reasoning to provide contextual, ranked suggestions.

---

## How It Works

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        TACTIC SUGGESTION PIPELINE                           │
│                                                                              │
│  ┌──────────┐    ┌──────────┐    ┌──────────┐    ┌──────────┐             │
│  │  LEAN4   │───►│  PARSE   │───►│   AI     │───►│  RANK &  │             │
│  │   LSP    │    │  GOALS   │    │ ANALYZE  │    │  FILTER  │             │
│  └──────────┘    └──────────┘    └──────────┘    └──────────┘             │
│       │               │               │               │                     │
│       ▼               ▼               ▼               ▼                     │
│  Goal state      Structured       Candidate       Top 5                    │
│  from cursor     goal + ctx       tactics         suggestions              │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Visual Design

### Suggestions Panel

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  TACTIC SUGGESTIONS                                         [⟳ Refresh]    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Current Goal:                                                              │
│  ⊢ valid_session (refresh_session s t)                                     │
│                                                                             │
│  Context:                                                                   │
│    s : Session                                                              │
│    t : Token                                                                │
│    hs : valid_session s                                                     │
│    ht : valid_token t                                                       │
│                                                                             │
│  ┌─ SUGGESTIONS ─────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ┌────────────────────────────────────────────────────────────────┐   │ │
│  │  │  1. unfold refresh_session                        ★★★★☆  95%  │   │ │
│  │  │                                                                 │   │ │
│  │  │  Expands the definition of refresh_session, revealing the      │   │ │
│  │  │  structure needed to prove validity.                           │   │ │
│  │  │                                                                 │   │ │
│  │  │  [Apply]  [Preview]  [Explain More]                            │   │ │
│  │  └────────────────────────────────────────────────────────────────┘   │ │
│  │                                                                        │ │
│  │  ┌────────────────────────────────────────────────────────────────┐   │ │
│  │  │  2. simp [valid_session, refresh_session]         ★★★★☆  88%  │   │ │
│  │  │                                                                 │   │ │
│  │  │  Simplifies using definitions. May complete proof or reduce    │   │ │
│  │  │  to simpler subgoals.                                          │   │ │
│  │  │                                                                 │   │ │
│  │  │  [Apply]  [Preview]  [Explain More]                            │   │ │
│  │  └────────────────────────────────────────────────────────────────┘   │ │
│  │                                                                        │ │
│  │  ┌────────────────────────────────────────────────────────────────┐   │ │
│  │  │  3. apply refresh_preserves_validity              ★★★☆☆  72%  │   │ │
│  │  │                                                                 │   │ │
│  │  │  Uses an existing lemma about refresh preserving validity.     │   │ │
│  │  │  Requires: valid_session s ∧ valid_token t                     │   │ │
│  │  │                                                                 │   │ │
│  │  │  [Apply]  [Preview]  [Explain More]                            │   │ │
│  │  └────────────────────────────────────────────────────────────────┘   │ │
│  │                                                                        │ │
│  │  [Show More Suggestions]  [Ask AI for Help]                           │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Preview Modal

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  PREVIEW: unfold refresh_session                                       [✕] │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Before applying:                                                          │
│  ┌─────────────────────────────────────────────────────────────────────┐  │
│  │  ⊢ valid_session (refresh_session s t)                              │  │
│  └─────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  After applying:                                                           │
│  ┌─────────────────────────────────────────────────────────────────────┐  │
│  │  ⊢ valid_session { s with token := t, refreshedAt := now }         │  │
│  └─────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  Explanation:                                                              │
│  The unfold tactic expands the definition of refresh_session,             │
│  showing that it creates a new session with the token field               │
│  updated. This reveals the structure you need to prove valid.             │
│                                                                             │
│  Next likely tactics:                                                      │
│  • simp [valid_session] - simplify the goal                               │
│  • constructor - if valid_session is a structure                          │
│  • exact ⟨hs.1, ht⟩ - provide witnesses directly                          │
│                                                                             │
│  [Cancel]                                                    [Apply Tactic] │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Data Model

```typescript
interface ProofGoal {
  index: number;
  type: string;  // The goal type to prove
  context: ContextItem[];  // Hypotheses and local definitions
  file: string;
  line: number;
  column: number;
}

interface ContextItem {
  name: string;
  type: string;
  value?: string;  // For let-bindings
  isHypothesis: boolean;
}

interface TacticSuggestion {
  id: string;
  tactic: string;
  confidence: number;  // 0-1
  description: string;
  explanation: string;
  
  // Preview information
  resultingGoals?: ProofGoal[];  // What goals remain after applying
  completesProof: boolean;
  
  // Source
  source: 'ai' | 'lsp' | 'library';
  
  // For library tactics
  lemmaName?: string;
  lemmaType?: string;
}

interface SuggestionRequest {
  goal: ProofGoal;
  file: string;
  imports: string[];  // Available lemmas
  previousTactics: string[];  // What's been tried
}
```

---

## PureScript Types

```purescript
module Sidepanel.Components.Proofs.TacticSuggestions where

import Prelude
import Data.Array (Array)
import Data.Maybe (Maybe)

type ProofGoal =
  { index :: Int
  , goalType :: String
  , context :: Array ContextItem
  , file :: String
  , line :: Int
  , column :: Int
  }

type ContextItem =
  { name :: String
  , itemType :: String
  , value :: Maybe String
  , isHypothesis :: Boolean
  }

type TacticSuggestion =
  { id :: String
  , tactic :: String
  , confidence :: Number
  , description :: String
  , explanation :: String
  , completesProof :: Boolean
  , source :: SuggestionSource
  }

data SuggestionSource = AIGenerated | LSPCompletion | LibraryLemma

type State =
  { currentGoal :: Maybe ProofGoal
  , suggestions :: Array TacticSuggestion
  , isLoading :: Boolean
  , selectedIndex :: Int
  , previewTactic :: Maybe TacticSuggestion
  , error :: Maybe String
  }

data Action
  = Initialize
  | SetGoal ProofGoal
  | RefreshSuggestions
  | SuggestionsLoaded (Array TacticSuggestion)
  | SelectSuggestion Int
  | ApplySuggestion TacticSuggestion
  | PreviewSuggestion TacticSuggestion
  | ClosePreview
  | AskAIForHelp
  | ShowMoreSuggestions

data Output
  = TacticApplied String
  | AIHelpRequested ProofGoal
```

---

## AI Suggestion Generation

### Bridge Service

```typescript
// bridge/src/proofs/tactic-suggester.ts

export class TacticSuggester {
  private veniceClient: VeniceClient;
  private lspClient: LeanLSPClient;
  
  async getSuggestions(request: SuggestionRequest): Promise<TacticSuggestion[]> {
    // Get suggestions from multiple sources
    const [aiSuggestions, lspSuggestions, librarySuggestions] = await Promise.all([
      this.getAISuggestions(request),
      this.getLSPCompletions(request),
      this.searchLibrary(request)
    ]);
    
    // Merge and rank
    const all = [...aiSuggestions, ...lspSuggestions, ...librarySuggestions];
    return this.rankSuggestions(all, request);
  }
  
  private async getAISuggestions(request: SuggestionRequest): Promise<TacticSuggestion[]> {
    const prompt = this.buildPrompt(request);
    
    const response = await this.veniceClient.chat({
      model: 'llama-3.3-70b',
      messages: [
        { role: 'system', content: TACTIC_SYSTEM_PROMPT },
        { role: 'user', content: prompt }
      ],
      max_tokens: 1000
    });
    
    return this.parseTacticResponse(response.choices[0].message.content);
  }
  
  private buildPrompt(request: SuggestionRequest): string {
    const contextStr = request.goal.context
      .map(c => `  ${c.name} : ${c.type}${c.value ? ` := ${c.value}` : ''}`)
      .join('\n');
    
    return `
Given the following Lean 4 proof goal:

Goal: ${request.goal.type}

Context:
${contextStr}

Previously tried tactics: ${request.previousTactics.join(', ') || 'none'}

Suggest up to 5 tactics that could help make progress on this goal.
For each suggestion, provide:
1. The exact tactic code
2. Confidence level (0-100)
3. Brief description of what it does
4. Why it might work for this goal

Format as JSON array.
`;
  }
  
  private async getLSPCompletions(request: SuggestionRequest): Promise<TacticSuggestion[]> {
    // Get completions from Lean LSP at cursor position
    const completions = await this.lspClient.getCompletions(
      request.file,
      request.goal.line,
      request.goal.column
    );
    
    return completions
      .filter(c => c.kind === 'tactic')
      .map(c => ({
        id: generateId(),
        tactic: c.label,
        confidence: 0.5,  // LSP completions are syntactically valid but may not help
        description: c.documentation || '',
        explanation: '',
        completesProof: false,
        source: 'lsp' as const
      }));
  }
  
  private async searchLibrary(request: SuggestionRequest): Promise<TacticSuggestion[]> {
    // Search for lemmas that match the goal pattern
    const results = await this.lspClient.search(request.goal.type);
    
    return results.map(r => ({
      id: generateId(),
      tactic: `exact ${r.name}` or `apply ${r.name}`,
      confidence: this.scoreMatch(r.type, request.goal.type),
      description: `Use lemma ${r.name}`,
      explanation: `This lemma has type: ${r.type}`,
      completesProof: false,
      source: 'library' as const,
      lemmaName: r.name,
      lemmaType: r.type
    }));
  }
  
  private rankSuggestions(
    suggestions: TacticSuggestion[],
    request: SuggestionRequest
  ): TacticSuggestion[] {
    // Score each suggestion
    const scored = suggestions.map(s => ({
      suggestion: s,
      score: this.computeScore(s, request)
    }));
    
    // Sort by score, take top 5
    return scored
      .sort((a, b) => b.score - a.score)
      .slice(0, 5)
      .map(s => s.suggestion);
  }
  
  private computeScore(suggestion: TacticSuggestion, request: SuggestionRequest): number {
    let score = suggestion.confidence;
    
    // Boost AI suggestions slightly (they're context-aware)
    if (suggestion.source === 'ai') {
      score *= 1.2;
    }
    
    // Penalize previously tried tactics
    if (request.previousTactics.includes(suggestion.tactic)) {
      score *= 0.1;
    }
    
    // Boost tactics that match common patterns
    if (this.matchesCommonPattern(suggestion.tactic, request.goal)) {
      score *= 1.3;
    }
    
    return Math.min(score, 1);  // Cap at 1
  }
}

const TACTIC_SYSTEM_PROMPT = `You are a Lean 4 proof assistant. Your job is to suggest tactics that will help make progress on proof goals.

Guidelines:
- Prefer simple tactics over complex ones
- Consider the context (hypotheses) carefully
- unfold, simp, and intro are often good starting points
- exact and apply are useful when you have matching lemmas
- constructor works well for inductive types
- induction and cases for recursive proofs

Always explain WHY a tactic might work, not just what it does.`;
```

---

## Tactic Preview

```typescript
// Get preview of what applying a tactic would do
async previewTactic(
  file: string,
  position: Position,
  tactic: string
): Promise<TacticPreview> {
  // Use Lean's tactic preview feature (if available)
  // or simulate by applying and reverting
  
  const result = await this.lspClient.request('lean/tacticPreview', {
    textDocument: { uri: file },
    position,
    tactic
  });
  
  return {
    resultingGoals: result.goals,
    completesProof: result.goals.length === 0,
    error: result.error
  };
}
```

---

## Component Implementation

```purescript
component :: forall q m. MonadAff m => H.Component q ProofGoal Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< SetGoal
      }
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "tactic-suggestions") ]
    [ renderGoalInfo state.currentGoal
    , case state.isLoading of
        true -> renderLoading
        false -> renderSuggestionsList state
    , renderActions
    , case state.previewTactic of
        Just tactic -> renderPreviewModal tactic
        Nothing -> HH.text ""
    ]

renderSuggestionsList :: forall m. State -> H.ComponentHTML Action () m
renderSuggestionsList state =
  HH.div
    [ HP.class_ (H.ClassName "suggestions-list") ]
    (mapWithIndex (renderSuggestion state.selectedIndex) state.suggestions)

renderSuggestion :: forall m. Int -> Int -> TacticSuggestion -> H.ComponentHTML Action () m
renderSuggestion selectedIdx idx suggestion =
  HH.div
    [ HP.classes $ suggestionClasses (selectedIdx == idx)
    , HE.onClick \_ -> SelectSuggestion idx
    ]
    [ HH.div
        [ HP.class_ (H.ClassName "suggestion__header") ]
        [ HH.span [ HP.class_ (H.ClassName "suggestion__rank") ]
            [ HH.text $ show (idx + 1) <> "." ]
        , HH.code [ HP.class_ (H.ClassName "suggestion__tactic") ]
            [ HH.text suggestion.tactic ]
        , renderConfidence suggestion.confidence
        ]
    , HH.div
        [ HP.class_ (H.ClassName "suggestion__description") ]
        [ HH.text suggestion.description ]
    , HH.div
        [ HP.class_ (H.ClassName "suggestion__actions") ]
        [ HH.button
            [ HP.classes [ H.ClassName "btn", H.ClassName "btn--primary", H.ClassName "btn--sm" ]
            , HE.onClick \_ -> ApplySuggestion suggestion
            ]
            [ HH.text "Apply" ]
        , HH.button
            [ HP.classes [ H.ClassName "btn", H.ClassName "btn--secondary", H.ClassName "btn--sm" ]
            , HE.onClick \_ -> PreviewSuggestion suggestion
            ]
            [ HH.text "Preview" ]
        ]
    ]

renderConfidence :: forall m. Number -> H.ComponentHTML Action () m
renderConfidence conf =
  let 
    stars = round (conf * 5.0)
    percent = round (conf * 100.0)
  in
    HH.span
      [ HP.class_ (H.ClassName "suggestion__confidence") ]
      [ HH.span [ HP.class_ (H.ClassName "stars") ]
          [ HH.text $ String.take stars "★★★★★" <> String.take (5 - stars) "☆☆☆☆☆" ]
      , HH.span [ HP.class_ (H.ClassName "percent") ]
          [ HH.text $ show percent <> "%" ]
      ]
```

---

## CSS Styling

```css
.tactic-suggestions {
  padding: var(--space-4);
}

.suggestions-list {
  display: flex;
  flex-direction: column;
  gap: var(--space-2);
}

.suggestion {
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: 8px;
  padding: var(--space-3);
  cursor: pointer;
  transition: all var(--transition-fast);
}

.suggestion:hover {
  border-color: var(--color-primary-dim);
}

.suggestion--selected {
  border-color: var(--color-primary);
  background: var(--color-primary-dim);
}

.suggestion__header {
  display: flex;
  align-items: center;
  gap: var(--space-2);
  margin-bottom: var(--space-2);
}

.suggestion__rank {
  font-weight: var(--font-weight-bold);
  color: var(--color-text-tertiary);
}

.suggestion__tactic {
  flex: 1;
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  color: var(--color-primary);
  background: var(--color-bg-base);
  padding: var(--space-1) var(--space-2);
  border-radius: 4px;
}

.suggestion__confidence {
  display: flex;
  align-items: center;
  gap: var(--space-1);
  font-size: var(--font-size-xs);
}

.suggestion__confidence .stars {
  color: var(--color-warning);
}

.suggestion__confidence .percent {
  color: var(--color-text-tertiary);
}

.suggestion__description {
  font-size: var(--font-size-sm);
  color: var(--color-text-secondary);
  margin-bottom: var(--space-2);
}

.suggestion__actions {
  display: flex;
  gap: var(--space-2);
}
```

---

## Related Specifications

- `60-LEAN4-INTEGRATION-OVERVIEW.md` - Lean4 overview
- `61-PROOF-PANEL.md` - Proof display
- `10-VENICE-API-OVERVIEW.md` - AI API

---

*"AI-powered proofs: human intuition amplified by machine reasoning."*
