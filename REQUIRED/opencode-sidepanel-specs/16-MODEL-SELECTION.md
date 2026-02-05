# 16-MODEL-SELECTION: Model Picker and Comparison

## Overview

Model Selection provides an interface for choosing between Venice's available models, comparing their capabilities, costs, and speeds to help users make informed decisions.

---

## Venice Model Zoo

Venice offers a variety of models optimized for different use cases. This interface surfaces that choice clearly.

---

## Visual Design

### Model Selector (Compact)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  MODEL: llama-3.3-70b ▼                                                     │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ QUICK SELECT ────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ● llama-3.3-70b        Best overall       ████████████ 70B            │ │
│  │  ○ qwen-2.5-72b         Strong reasoning   ████████████ 72B            │ │
│  │  ○ deepseek-r1-70b      Excellent code     ████████████ 70B            │ │
│  │  ○ llama-3.1-405b       Maximum power      ████████████████████ 405B   │ │
│  │  ○ qwen-2.5-7b          Fast & cheap       ████ 7B                     │ │
│  │                                                                        │ │
│  │  [Show All Models...]  [Compare...]                                   │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Full Model Picker

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  SELECT MODEL                                                         [✕]  │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─ FILTERS ─────────────────────────────────────────────────────────────┐ │
│  │  Size: [All ▼]   Type: [All ▼]   Speed: [All ▼]   [🔍 Search...]     │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ FEATURED ────────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ┌──────────────────────────────────────────────────────────────────┐ │ │
│  │  │  ⭐ RECOMMENDED                                                   │ │ │
│  │  │  llama-3.3-70b                                                   │ │ │
│  │  │                                                                   │ │ │
│  │  │  Best balance of capability and cost for most coding tasks.     │ │ │
│  │  │                                                                   │ │ │
│  │  │  Speed: ████████░░ Fast        Context: 128K tokens              │ │ │
│  │  │  Quality: █████████░ Excellent  Cost: ~0.1 Diem/1K tokens        │ │ │
│  │  │                                                                   │ │ │
│  │  │  Best for: General coding, debugging, explanations              │ │ │
│  │  │                                                      [Select]    │ │ │
│  │  └──────────────────────────────────────────────────────────────────┘ │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ ALL MODELS ──────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  ┌─ LARGE (70B+) ─────────────────────────────────────────────────┐  │ │
│  │  │                                                                 │  │ │
│  │  │  llama-3.1-405b                           Speed: ██░░░░░░░░    │  │ │
│  │  │  Maximum capability, slower               Quality: ██████████  │  │ │
│  │  │  Best for: Complex architecture, deep analysis                 │  │ │
│  │  │                                                      [Select]  │  │ │
│  │  │                                                                 │  │ │
│  │  │  deepseek-r1-70b                          Speed: ████████░░    │  │ │
│  │  │  Excellent at code generation             Quality: █████████░  │  │ │
│  │  │  Best for: Code generation, refactoring                        │  │ │
│  │  │                                                      [Select]  │  │ │
│  │  │                                                                 │  │ │
│  │  │  qwen-2.5-72b                             Speed: ████████░░    │  │ │
│  │  │  Strong reasoning and math                Quality: █████████░  │  │ │
│  │  │  Best for: Algorithms, math proofs                             │  │ │
│  │  │                                                      [Select]  │  │ │
│  │  │                                                                 │  │ │
│  │  └─────────────────────────────────────────────────────────────────┘  │ │
│  │                                                                        │ │
│  │  ┌─ MEDIUM (7B-30B) ──────────────────────────────────────────────┐  │ │
│  │  │                                                                 │  │ │
│  │  │  qwen-2.5-32b                             Speed: █████████░    │  │ │
│  │  │  Good balance for medium tasks            Quality: ████████░░  │  │ │
│  │  │  Best for: Quick questions, simple code                        │  │ │
│  │  │                                                      [Select]  │  │ │
│  │  │                                                                 │  │ │
│  │  │  qwen-2.5-7b                              Speed: ██████████    │  │ │
│  │  │  Very fast, lightweight                   Quality: ██████░░░░  │  │ │
│  │  │  Best for: Simple tasks, high volume                           │  │ │
│  │  │                                                      [Select]  │  │ │
│  │  │                                                                 │  │ │
│  │  └─────────────────────────────────────────────────────────────────┘  │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  Currently selected: llama-3.3-70b                                         │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Model Comparison

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  COMPARE MODELS                                                       [✕]  │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Select models to compare: [llama-3.3-70b ▼] vs [deepseek-r1-70b ▼]       │
│                                                                             │
│  ┌─ COMPARISON ──────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │                    llama-3.3-70b      deepseek-r1-70b                 │ │
│  │  ─────────────────────────────────────────────────────────────────   │ │
│  │  Parameters       70B                 70B                             │ │
│  │  Context          128K                64K                             │ │
│  │  Speed            ████████░░          █████████░                      │ │
│  │  Quality          █████████░          █████████░                      │ │
│  │  Cost/1K tokens   ~0.10 Diem          ~0.08 Diem                     │ │
│  │                                                                        │ │
│  │  Best For         General purpose     Code-focused                    │ │
│  │                   Debugging           Generation                      │ │
│  │                   Explanation         Refactoring                     │ │
│  │                                                                        │ │
│  │  Weaknesses       Slightly slower     Smaller context                 │ │
│  │                   on generation       Less versatile                  │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  💡 For your current task (debugging), llama-3.3-70b is recommended.      │
│                                                                             │
│  [Select llama-3.3-70b]              [Select deepseek-r1-70b]             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Data Model

```typescript
interface Model {
  id: string;
  name: string;
  displayName: string;
  provider: 'venice';
  
  // Specs
  parameters: string;  // "70B", "7B", etc.
  contextWindow: number;
  
  // Ratings (1-10)
  speedRating: number;
  qualityRating: number;
  
  // Cost
  inputCostPer1K: number;   // Diem per 1K input tokens
  outputCostPer1K: number;  // Diem per 1K output tokens
  
  // Capabilities
  bestFor: string[];
  weaknesses: string[];
  
  // UI
  category: 'large' | 'medium' | 'small';
  recommended: boolean;
  description: string;
}

interface ModelSelection {
  currentModelId: string;
  recentModels: string[];
  favoriteModels: string[];
}

interface ModelEstimate {
  model: Model;
  estimatedInputTokens: number;
  estimatedOutputTokens: number;
  estimatedCost: number;
  estimatedTime: string;
}
```

---

## Model Data

```typescript
const VENICE_MODELS: Model[] = [
  {
    id: 'llama-3.3-70b',
    name: 'llama-3.3-70b',
    displayName: 'Llama 3.3 70B',
    provider: 'venice',
    parameters: '70B',
    contextWindow: 128000,
    speedRating: 8,
    qualityRating: 9,
    inputCostPer1K: 0.08,
    outputCostPer1K: 0.12,
    bestFor: ['General coding', 'Debugging', 'Explanations', 'Documentation'],
    weaknesses: ['Slightly slower on large generations'],
    category: 'large',
    recommended: true,
    description: 'Best overall model for most coding tasks. Excellent balance of speed, quality, and cost.'
  },
  {
    id: 'llama-3.1-405b',
    name: 'llama-3.1-405b',
    displayName: 'Llama 3.1 405B',
    provider: 'venice',
    parameters: '405B',
    contextWindow: 128000,
    speedRating: 3,
    qualityRating: 10,
    inputCostPer1K: 0.30,
    outputCostPer1K: 0.45,
    bestFor: ['Complex architecture', 'Deep analysis', 'Difficult problems'],
    weaknesses: ['Slow', 'Expensive', 'Overkill for simple tasks'],
    category: 'large',
    recommended: false,
    description: 'Maximum capability for the most challenging tasks. Use sparingly.'
  },
  {
    id: 'deepseek-r1-70b',
    name: 'deepseek-r1-70b',
    displayName: 'DeepSeek R1 70B',
    provider: 'venice',
    parameters: '70B',
    contextWindow: 64000,
    speedRating: 9,
    qualityRating: 9,
    inputCostPer1K: 0.06,
    outputCostPer1K: 0.10,
    bestFor: ['Code generation', 'Refactoring', 'Algorithm design'],
    weaknesses: ['Smaller context window', 'Less versatile'],
    category: 'large',
    recommended: false,
    description: 'Excellent for pure code tasks. Fast and cost-effective.'
  },
  {
    id: 'qwen-2.5-72b',
    name: 'qwen-2.5-72b',
    displayName: 'Qwen 2.5 72B',
    provider: 'venice',
    parameters: '72B',
    contextWindow: 128000,
    speedRating: 8,
    qualityRating: 9,
    inputCostPer1K: 0.08,
    outputCostPer1K: 0.12,
    bestFor: ['Mathematical reasoning', 'Algorithm analysis', 'Proofs'],
    weaknesses: ['Slightly less creative'],
    category: 'large',
    recommended: false,
    description: 'Strong reasoning capabilities. Great for math-heavy tasks.'
  },
  {
    id: 'qwen-2.5-32b',
    name: 'qwen-2.5-32b',
    displayName: 'Qwen 2.5 32B',
    provider: 'venice',
    parameters: '32B',
    contextWindow: 64000,
    speedRating: 9,
    qualityRating: 7,
    inputCostPer1K: 0.03,
    outputCostPer1K: 0.05,
    bestFor: ['Quick questions', 'Simple code', 'Drafts'],
    weaknesses: ['Less capable on complex tasks'],
    category: 'medium',
    recommended: false,
    description: 'Good balance for medium-complexity tasks. Fast and affordable.'
  },
  {
    id: 'qwen-2.5-7b',
    name: 'qwen-2.5-7b',
    displayName: 'Qwen 2.5 7B',
    provider: 'venice',
    parameters: '7B',
    contextWindow: 32000,
    speedRating: 10,
    qualityRating: 5,
    inputCostPer1K: 0.01,
    outputCostPer1K: 0.02,
    bestFor: ['Simple questions', 'Formatting', 'High volume'],
    weaknesses: ['Limited reasoning', 'Not for complex code'],
    category: 'small',
    recommended: false,
    description: 'Very fast and cheap. Use for simple, repetitive tasks.'
  }
];
```

---

## PureScript Component

```purescript
module Sidepanel.Components.ModelSelector where

type Model =
  { id :: String
  , name :: String
  , displayName :: String
  , parameters :: String
  , contextWindow :: Int
  , speedRating :: Int
  , qualityRating :: Int
  , bestFor :: Array String
  , category :: ModelCategory
  , recommended :: Boolean
  , description :: String
  }

data ModelCategory = Large | Medium | Small

type State =
  { models :: Array Model
  , currentModelId :: String
  , isExpanded :: Boolean
  , showComparison :: Boolean
  , compareModelIds :: Maybe (Tuple String String)
  , filter :: ModelFilter
  }

type ModelFilter =
  { category :: Maybe ModelCategory
  , minSpeed :: Int
  , minQuality :: Int
  , searchQuery :: String
  }

data Action
  = ToggleExpanded
  | SelectModel String
  | ShowComparison String String
  | HideComparison
  | SetFilter ModelFilter
  | SetSearchQuery String

renderModelCard :: forall m. Model -> Boolean -> H.ComponentHTML Action () m
renderModelCard model isSelected =
  HH.div
    [ HP.classes $ modelCardClasses isSelected model.recommended ]
    [ when model.recommended $
        HH.div [ HP.class_ (H.ClassName "model-badge") ] [ HH.text "⭐ RECOMMENDED" ]
    , HH.div [ HP.class_ (H.ClassName "model-card__name") ] [ HH.text model.displayName ]
    , HH.div [ HP.class_ (H.ClassName "model-card__description") ] [ HH.text model.description ]
    , HH.div
        [ HP.class_ (H.ClassName "model-card__stats") ]
        [ renderRating "Speed" model.speedRating
        , renderRating "Quality" model.qualityRating
        , HH.div_ [ HH.text $ "Context: " <> formatNumber model.contextWindow <> " tokens" ]
        ]
    , HH.div
        [ HP.class_ (H.ClassName "model-card__best-for") ]
        [ HH.text $ "Best for: " <> intercalate ", " model.bestFor ]
    , HH.button
        [ HP.classes [ H.ClassName "btn", H.ClassName "btn--primary" ]
        , HE.onClick \_ -> SelectModel model.id
        ]
        [ HH.text $ if isSelected then "Selected" else "Select" ]
    ]

renderRating :: forall m. String -> Int -> H.ComponentHTML Action () m
renderRating label rating =
  HH.div
    [ HP.class_ (H.ClassName "rating") ]
    [ HH.span_ [ HH.text $ label <> ": " ]
    , HH.span [ HP.class_ (H.ClassName "rating-bar") ]
        [ HH.span
            [ HP.class_ (H.ClassName "rating-fill")
            , HP.style $ "width: " <> show (rating * 10) <> "%"
            ]
            []
        ]
    ]
```

---

## Smart Model Suggestions

```typescript
// Suggest model based on task type
function suggestModel(taskType: string, contextSize: number): Model {
  // Large context needs
  if (contextSize > 64000) {
    return models.find(m => m.contextWindow >= 128000 && m.recommended);
  }
  
  // Task-specific suggestions
  switch (taskType) {
    case 'code_generation':
      return models.find(m => m.id === 'deepseek-r1-70b');
    case 'math_reasoning':
      return models.find(m => m.id === 'qwen-2.5-72b');
    case 'simple_question':
      return models.find(m => m.id === 'qwen-2.5-7b');
    case 'complex_analysis':
      return models.find(m => m.id === 'llama-3.1-405b');
    default:
      return models.find(m => m.recommended);
  }
}
```

---

## Related Specifications

- `10-VENICE-API-OVERVIEW.md` - Venice API details
- `15-COST-PROJECTION.md` - Cost estimation
- `55-SETTINGS-PANEL.md` - Model preferences

---

*"The right model for the right task. Don't overpay for overkill."*
