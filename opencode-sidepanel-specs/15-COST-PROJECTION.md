# 15-COST-PROJECTION: Forecasting and Budget Management

## Overview

Cost Projection provides intelligent forecasting of Diem consumption, helping users understand when they'll run out of credits and how to optimize their usage.

---

## Key Questions Answered

1. "When will I run out of Diem?"
2. "Can I finish this task before reset?"
3. "How much is this conversation costing?"
4. "Am I using more than usual?"

---

## Visual Design

### Projection Widget (Dashboard)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  PROJECTED USAGE                                              [Settings ⚙] │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  Current Balance: 42.5 Diem                                                │
│  Current Rate: 5.2 Diem/hour                                               │
│                                                                             │
│  ┌─ PROJECTION ──────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  50 ┤                                                                  │ │
│  │     │ ●                                                                │ │
│  │  40 ┤  ╲                                                               │ │
│  │     │   ╲                                                              │ │
│  │  30 ┤    ╲                                                             │ │
│  │     │     ╲──────────                                                  │ │
│  │  20 ┤            ╲                                                     │ │
│  │     │             ╲                                                    │ │
│  │  10 ┤              ╲                                                   │ │
│  │     │               ╲─ ─ ─ ─ ─ ─ ⚠                                    │ │
│  │   0 ┼────────────────────────────────────────                         │ │
│  │     Now   +2h    +4h    +6h    +8h   Reset                            │ │
│  │                                                                        │ │
│  │  ── Projected usage  ─ ─ Warning zone  │ Reset time                   │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  ┌─ SCENARIOS ───────────────────────────────────────────────────────────┐ │
│  │                                                                        │ │
│  │  At current rate (5.2/hr):    Runs out at ~6:10 PM (2h before reset) │ │
│  │  If you slow down (3/hr):     Makes it to reset with 12 Diem left    │ │
│  │  If you speed up (8/hr):      Runs out at ~3:30 PM                   │ │
│  │                                                                        │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                             │
│  💡 At your current pace, you'll run out before reset.                     │
│     Consider using smaller models for simple tasks.                        │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Cost Estimator (Before Sending)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                                                                             │
│  Estimated Cost for This Message                                           │
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐  │
│  │                                                                       │  │
│  │  Input Tokens:     ~2,500 (context + your message)                   │  │
│  │  Expected Output:  ~1,000 (based on query type)                      │  │
│  │  Model:            llama-3.3-70b                                     │  │
│  │                                                                       │  │
│  │  ───────────────────────────────────────────────────────────────     │  │
│  │  Estimated Cost:   0.35 Diem ($0.35)                                 │  │
│  │  After This:       42.15 Diem remaining                              │  │
│  │                                                                       │  │
│  └─────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  💡 Using a smaller model (qwen-2.5-7b) would cost ~0.08 Diem             │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Algorithms

### Consumption Rate Calculation

```typescript
interface ConsumptionSnapshot {
  timestamp: Date;
  balance: number;
}

function calculateConsumptionRate(snapshots: ConsumptionSnapshot[]): number {
  if (snapshots.length < 2) return 0;
  
  // Use weighted average favoring recent data
  const weights = [0.5, 0.3, 0.2];  // Most recent gets highest weight
  let totalWeightedRate = 0;
  let totalWeight = 0;
  
  // Calculate rate between consecutive pairs
  for (let i = 0; i < Math.min(snapshots.length - 1, weights.length); i++) {
    const newer = snapshots[snapshots.length - 1 - i];
    const older = snapshots[snapshots.length - 2 - i];
    
    const timeDiffHours = (newer.timestamp.getTime() - older.timestamp.getTime()) / (1000 * 60 * 60);
    const balanceDiff = older.balance - newer.balance;
    
    // Skip if balance increased (reset or deposit)
    if (balanceDiff < 0) continue;
    
    const rate = balanceDiff / timeDiffHours;
    totalWeightedRate += rate * weights[i];
    totalWeight += weights[i];
  }
  
  return totalWeight > 0 ? totalWeightedRate / totalWeight : 0;
}
```

### Time to Depletion

```typescript
function calculateTimeToDepletion(
  currentBalance: number,
  consumptionRate: number,  // per hour
  resetTime: Date
): DepletionPrediction {
  if (consumptionRate <= 0) {
    return {
      willDeplete: false,
      hoursRemaining: Infinity,
      depletionTime: null,
      willMakeItToReset: true,
      balanceAtReset: currentBalance
    };
  }
  
  const hoursToDepletion = currentBalance / consumptionRate;
  const depletionTime = new Date(Date.now() + hoursToDepletion * 60 * 60 * 1000);
  const hoursToReset = (resetTime.getTime() - Date.now()) / (1000 * 60 * 60);
  
  const willMakeItToReset = hoursToDepletion > hoursToReset;
  const balanceAtReset = willMakeItToReset 
    ? currentBalance - (consumptionRate * hoursToReset)
    : 0;
  
  return {
    willDeplete: true,
    hoursRemaining: hoursToDepletion,
    depletionTime,
    willMakeItToReset,
    balanceAtReset: Math.max(0, balanceAtReset)
  };
}
```

### Message Cost Estimation

```typescript
interface CostEstimate {
  inputTokens: number;
  outputTokens: number;
  totalTokens: number;
  estimatedCost: number;
  confidence: 'high' | 'medium' | 'low';
}

function estimateMessageCost(
  message: string,
  context: ContextEntry[],
  model: string,
  queryType: QueryType
): CostEstimate {
  // Estimate input tokens
  const messageTokens = estimateTokens(message);
  const contextTokens = context.reduce((sum, c) => sum + c.tokens, 0);
  const systemPromptTokens = 500;  // Approximate
  const inputTokens = messageTokens + contextTokens + systemPromptTokens;
  
  // Estimate output based on query type
  const outputMultipliers = {
    simple_question: 0.3,      // Short answer
    explanation: 0.8,          // Medium explanation
    code_generation: 1.5,      // Code is verbose
    debugging: 1.2,            // Analysis + fix
    refactoring: 2.0,          // Large code blocks
  };
  
  const outputTokens = Math.round(inputTokens * (outputMultipliers[queryType] ?? 1.0));
  
  // Get model pricing
  const pricing = getModelPricing(model);
  const cost = (inputTokens / 1000 * pricing.inputPer1K) + 
               (outputTokens / 1000 * pricing.outputPer1K);
  
  // Confidence based on context size and query type
  const confidence = contextTokens < 1000 ? 'high' : contextTokens < 5000 ? 'medium' : 'low';
  
  return {
    inputTokens,
    outputTokens,
    totalTokens: inputTokens + outputTokens,
    estimatedCost: cost,
    confidence
  };
}

function estimateTokens(text: string): number {
  // Rough estimate: 1 token ≈ 4 characters
  return Math.ceil(text.length / 4);
}
```

### Scenario Projections

```typescript
interface Scenario {
  name: string;
  rate: number;  // Diem per hour
  prediction: DepletionPrediction;
}

function generateScenarios(
  currentBalance: number,
  currentRate: number,
  resetTime: Date
): Scenario[] {
  const rates = [
    { name: 'Light usage', factor: 0.5 },
    { name: 'Current pace', factor: 1.0 },
    { name: 'Heavy usage', factor: 1.5 },
  ];
  
  return rates.map(r => ({
    name: r.name,
    rate: currentRate * r.factor,
    prediction: calculateTimeToDepletion(
      currentBalance,
      currentRate * r.factor,
      resetTime
    )
  }));
}
```

---

## PureScript Types

```purescript
module Sidepanel.Projection where

import Prelude
import Data.Maybe (Maybe)
import Data.DateTime (DateTime)

type ConsumptionSnapshot =
  { timestamp :: DateTime
  , balance :: Number
  }

type DepletionPrediction =
  { willDeplete :: Boolean
  , hoursRemaining :: Number
  , depletionTime :: Maybe DateTime
  , willMakeItToReset :: Boolean
  , balanceAtReset :: Number
  }

type CostEstimate =
  { inputTokens :: Int
  , outputTokens :: Int
  , totalTokens :: Int
  , estimatedCost :: Number
  , confidence :: Confidence
  }

data Confidence = High | Medium | Low

type Scenario =
  { name :: String
  , rate :: Number
  , prediction :: DepletionPrediction
  }

type ProjectionState =
  { currentBalance :: Number
  , currentRate :: Number
  , resetTime :: DateTime
  , prediction :: DepletionPrediction
  , scenarios :: Array Scenario
  , chartData :: Array ChartPoint
  }

type ChartPoint =
  { time :: DateTime
  , projected :: Number
  , isWarningZone :: Boolean
  }
```

---

## Component Implementation

```purescript
module Sidepanel.Components.Projection where

component :: forall q m. MonadAff m => H.Component q BalanceState Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      }
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "projection-widget") ]
    [ renderHeader state
    , renderChart state.chartData
    , renderScenarios state.scenarios
    , renderRecommendation state.prediction
    ]

renderChart :: forall m. Array ChartPoint -> H.ComponentHTML Action () m
renderChart points =
  HH.div
    [ HP.class_ (H.ClassName "projection-chart")
    , HP.ref (H.RefLabel "chart-container")
    ]
    []

renderScenarios :: forall m. Array Scenario -> H.ComponentHTML Action () m
renderScenarios scenarios =
  HH.div
    [ HP.class_ (H.ClassName "projection-scenarios") ]
    [ HH.div [ HP.class_ (H.ClassName "scenarios-title") ] [ HH.text "Scenarios" ]
    , HH.div [ HP.class_ (H.ClassName "scenarios-list") ]
        (map renderScenario scenarios)
    ]

renderScenario :: forall m. Scenario -> H.ComponentHTML Action () m
renderScenario scenario =
  HH.div
    [ HP.class_ (H.ClassName "scenario") ]
    [ HH.span [ HP.class_ (H.ClassName "scenario-name") ]
        [ HH.text $ scenario.name <> " (" <> formatRate scenario.rate <> "/hr):" ]
    , HH.span [ HP.class_ (H.ClassName "scenario-prediction") ]
        [ HH.text $ formatPrediction scenario.prediction ]
    ]

renderRecommendation :: forall m. DepletionPrediction -> H.ComponentHTML Action () m
renderRecommendation prediction =
  let 
    (icon, message) = getRecommendation prediction
  in
    HH.div
      [ HP.class_ (H.ClassName "projection-recommendation") ]
      [ HH.span [ HP.class_ (H.ClassName "recommendation-icon") ] [ HH.text icon ]
      , HH.span [ HP.class_ (H.ClassName "recommendation-text") ] [ HH.text message ]
      ]

getRecommendation :: DepletionPrediction -> Tuple String String
getRecommendation prediction
  | not prediction.willDeplete =
      Tuple "✓" "You're using credits very slowly. Balance will last well beyond reset."
  | prediction.willMakeItToReset =
      Tuple "💡" $ "At your current pace, you'll have " <> 
                   formatDiem prediction.balanceAtReset <> " Diem left at reset."
  | prediction.hoursRemaining < 1.0 =
      Tuple "⚠" "Warning: You'll run out in less than an hour. Consider slowing down."
  | otherwise =
      Tuple "💡" $ "At your current pace, you'll run out before reset. " <>
                   "Consider using smaller models for simple tasks."
```

---

## Real-Time Updates

```typescript
// Update projections when balance changes
store.on('balance.update', (balance) => {
  const snapshots = snapshotStore.getRecentSnapshots(10);
  snapshots.push({ timestamp: new Date(), balance: balance.diem });
  
  const rate = calculateConsumptionRate(snapshots);
  const prediction = calculateTimeToDepletion(balance.diem, rate, getNextMidnightUTC());
  const scenarios = generateScenarios(balance.diem, rate, getNextMidnightUTC());
  const chartData = generateChartData(balance.diem, rate, getNextMidnightUTC());
  
  broadcastProjectionUpdate({ rate, prediction, scenarios, chartData });
});
```

---

## CSS Styling

```css
.projection-widget {
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: 8px;
  padding: var(--space-4);
}

.projection-chart {
  height: 200px;
  margin: var(--space-4) 0;
}

.projection-scenarios {
  background: var(--color-bg-base);
  border-radius: 6px;
  padding: var(--space-3);
  margin-bottom: var(--space-3);
}

.scenarios-title {
  font-size: var(--font-size-sm);
  font-weight: var(--font-weight-semibold);
  color: var(--color-text-secondary);
  margin-bottom: var(--space-2);
}

.scenario {
  display: flex;
  justify-content: space-between;
  font-size: var(--font-size-sm);
  padding: var(--space-1) 0;
}

.scenario-name {
  color: var(--color-text-secondary);
}

.scenario-prediction {
  color: var(--color-text-primary);
  font-family: var(--font-mono);
}

.projection-recommendation {
  display: flex;
  align-items: flex-start;
  gap: var(--space-2);
  padding: var(--space-3);
  background: var(--color-primary-dim);
  border-radius: 6px;
  font-size: var(--font-size-sm);
}

.recommendation-icon {
  font-size: 16px;
}
```

---

## Related Specifications

- `11-DIEM-TRACKING.md` - Balance tracking
- `12-DIEM-RESET-COUNTDOWN.md` - Reset timing
- `13-TOKEN-USAGE-METRICS.md` - Token metrics
- `53-TOKEN-USAGE-CHART.md` - Chart rendering

---

*"Know your burn rate. Plan your work. Finish before reset."*
