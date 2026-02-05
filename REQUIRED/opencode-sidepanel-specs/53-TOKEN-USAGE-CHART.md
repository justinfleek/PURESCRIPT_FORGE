# 53-TOKEN-USAGE-CHART: Usage Visualization Component

## Overview

The Token Usage Chart visualizes token consumption over time using Recharts. It shows prompt vs completion tokens, cost trends, and supports multiple time ranges.

---

## Chart Types

### 1. Line Chart (Primary)

Shows token usage over time with separate lines for prompt and completion tokens.

```
  Tokens
    │
 2k │     ╭─────╮
    │    ╱      ╲
 1k │   ╱        ╲────╮
    │  ╱              ╲
  0 │─╱────────────────╲───────
    └──────────────────────────
       9am   10am  11am  12pm
    
    ── Prompt   ── Completion
```

### 2. Area Chart (Stacked)

Shows cumulative usage with prompt and completion stacked.

### 3. Bar Chart (Hourly)

Shows hourly breakdown when viewing 24h range.

---

## Component Design

### Visual Layout

```
┌─────────────────────────────────────────────────────────┐
│  Token Usage                           [1h][24h][7d][All]│
├─────────────────────────────────────────────────────────┤
│                                                          │
│  3k ┤                                                    │
│     │            ╭────╮                                  │
│  2k ┤     ╭─────╯    ╲                                  │
│     │    ╱            ╲────────╮                        │
│  1k ┤   ╱                      ╲────                    │
│     │  ╱                                                │
│   0 ┼──┴────────────────────────────────────           │
│      9:00   10:00   11:00   12:00   1:00               │
│                                                          │
│  ── Prompt (15,234)  ── Completion (8,721)              │
└─────────────────────────────────────────────────────────┘
```

---

## PureScript Implementation

### Types

```purescript
module Sidepanel.Components.Usage.TokenChart where

import Prelude
import Data.DateTime (DateTime)
import Data.Array (Array)
import Foreign.Object (Object)

-- Data point for chart
type UsageDataPoint =
  { timestamp :: DateTime
  , promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  , cost :: Number
  }

-- Time range options
data TimeRange
  = LastHour
  | Last24Hours
  | Last7Days
  | AllTime

derive instance eqTimeRange :: Eq TimeRange

-- Chart display mode
data ChartMode = Line | Area | Bar

-- Component input
type Input =
  { data :: Array UsageDataPoint
  , timeRange :: TimeRange
  }

-- Component state
type State =
  { data :: Array UsageDataPoint
  , timeRange :: TimeRange
  , chartMode :: ChartMode
  , hoveredPoint :: Maybe UsageDataPoint
  , totals :: Totals
  }

type Totals =
  { promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  , cost :: Number
  }

-- Actions
data Action
  = Receive Input
  | SetTimeRange TimeRange
  | SetChartMode ChartMode
  | HandleHover (Maybe UsageDataPoint)
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
initialState { data: d, timeRange } =
  { data: d
  , timeRange
  , chartMode: Line
  , hoveredPoint: Nothing
  , totals: calculateTotals d
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "token-chart") ]
    [ -- Header with time range selector
      renderHeader state
    
    -- Chart container (Recharts via FFI)
    , HH.div
        [ HP.class_ (H.ClassName "token-chart__container")
        , HP.ref chartRef
        ]
        []  -- Chart rendered via FFI
    
    -- Legend with totals
    , renderLegend state.totals
    
    -- Tooltip (when hovering)
    , renderTooltip state.hoveredPoint
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.div
    [ HP.class_ (H.ClassName "token-chart__header") ]
    [ HH.span 
        [ HP.class_ (H.ClassName "token-chart__title") ]
        [ HH.text "Token Usage" ]
    , renderTimeRangeSelector state.timeRange
    ]

renderTimeRangeSelector :: forall m. TimeRange -> H.ComponentHTML Action () m
renderTimeRangeSelector current =
  HH.div
    [ HP.class_ (H.ClassName "time-range-selector") ]
    [ btn LastHour "1h"
    , btn Last24Hours "24h"
    , btn Last7Days "7d"
    , btn AllTime "All"
    ]
  where
    btn range label =
      HH.button
        [ HP.classes $ buttonClasses (range == current)
        , HE.onClick \_ -> SetTimeRange range
        ]
        [ HH.text label ]

renderLegend :: forall m. Totals -> H.ComponentHTML Action () m
renderLegend { promptTokens, completionTokens } =
  HH.div
    [ HP.class_ (H.ClassName "token-chart__legend") ]
    [ HH.div
        [ HP.class_ (H.ClassName "legend-item legend-item--prompt") ]
        [ HH.span [ HP.class_ (H.ClassName "legend-color") ] []
        , HH.text $ "Prompt (" <> formatNumber promptTokens <> ")"
        ]
    , HH.div
        [ HP.class_ (H.ClassName "legend-item legend-item--completion") ]
        [ HH.span [ HP.class_ (H.ClassName "legend-color") ] []
        , HH.text $ "Completion (" <> formatNumber completionTokens <> ")"
        ]
    ]

renderTooltip :: forall m. Maybe UsageDataPoint -> H.ComponentHTML Action () m
renderTooltip Nothing = HH.text ""
renderTooltip (Just point) =
  HH.div
    [ HP.class_ (H.ClassName "token-chart__tooltip") ]
    [ HH.div_ [ HH.text $ formatDateTime point.timestamp ]
    , HH.div_ [ HH.text $ "Prompt: " <> formatNumber point.promptTokens ]
    , HH.div_ [ HH.text $ "Completion: " <> formatNumber point.completionTokens ]
    , HH.div_ [ HH.text $ "Cost: " <> formatUSD point.cost ]
    ]

buttonClasses :: Boolean -> Array H.ClassName
buttonClasses selected =
  [ H.ClassName "time-range-btn" ] <>
  if selected then [ H.ClassName "time-range-btn--selected" ] else []
```

### Recharts FFI

```purescript
module Sidepanel.Utils.FFI.Recharts where

import Prelude
import Effect (Effect)
import Web.DOM.Element (Element)
import Foreign (Foreign)

-- Chart configuration
type ChartConfig =
  { data :: Array Foreign  -- UsageDataPoint as JS objects
  , width :: Int
  , height :: Int
  , mode :: String  -- "line" | "area" | "bar"
  , colors ::
      { prompt :: String
      , completion :: String
      }
  , onHover :: Foreign -> Effect Unit
  }

-- Render chart into element
foreign import renderChart :: Element -> ChartConfig -> Effect Unit

-- Update chart data
foreign import updateChartData :: Element -> Array Foreign -> Effect Unit

-- Destroy chart (cleanup)
foreign import destroyChart :: Element -> Effect Unit
```

```javascript
// FFI Implementation
import React from 'react';
import { createRoot } from 'react-dom/client';
import {
  LineChart, Line, XAxis, YAxis, CartesianGrid,
  Tooltip, Legend, ResponsiveContainer, Area, AreaChart
} from 'recharts';

const chartRoots = new WeakMap();

export const renderChart = element => config => () => {
  // Cleanup existing
  if (chartRoots.has(element)) {
    chartRoots.get(element).unmount();
  }

  const root = createRoot(element);
  chartRoots.set(element, root);

  const ChartComponent = config.mode === 'area' ? AreaChart : LineChart;

  root.render(
    <ResponsiveContainer width="100%" height={config.height}>
      <ChartComponent data={config.data}>
        <CartesianGrid strokeDasharray="3 3" stroke="#27272a" />
        <XAxis 
          dataKey="time" 
          stroke="#71717a"
          tick={{ fill: '#a1a1aa', fontSize: 12 }}
        />
        <YAxis 
          stroke="#71717a"
          tick={{ fill: '#a1a1aa', fontSize: 12 }}
          tickFormatter={v => v >= 1000 ? `${v/1000}k` : v}
        />
        <Tooltip 
          contentStyle={{
            background: '#242424',
            border: '1px solid #3f3f46',
            borderRadius: '6px'
          }}
        />
        {config.mode === 'area' ? (
          <>
            <Area 
              type="monotone" 
              dataKey="promptTokens" 
              stackId="1"
              stroke={config.colors.prompt}
              fill={config.colors.prompt}
              fillOpacity={0.3}
            />
            <Area 
              type="monotone" 
              dataKey="completionTokens"
              stackId="1"
              stroke={config.colors.completion}
              fill={config.colors.completion}
              fillOpacity={0.3}
            />
          </>
        ) : (
          <>
            <Line 
              type="monotone" 
              dataKey="promptTokens" 
              stroke={config.colors.prompt}
              strokeWidth={2}
              dot={false}
            />
            <Line 
              type="monotone" 
              dataKey="completionTokens" 
              stroke={config.colors.completion}
              strokeWidth={2}
              dot={false}
            />
          </>
        )}
      </ChartComponent>
    </ResponsiveContainer>
  );
};

export const updateChartData = element => data => () => {
  // Re-render with new data (React handles diffing)
  const root = chartRoots.get(element);
  if (root) {
    // Trigger re-render via state update pattern
  }
};

export const destroyChart = element => () => {
  if (chartRoots.has(element)) {
    chartRoots.get(element).unmount();
    chartRoots.delete(element);
  }
};
```

---

## Data Aggregation

### Time Range Filtering

```purescript
-- Filter data points by time range
filterByTimeRange :: TimeRange -> DateTime -> Array UsageDataPoint -> Array UsageDataPoint
filterByTimeRange range now points =
  let cutoff = case range of
        LastHour -> subtractHours 1 now
        Last24Hours -> subtractHours 24 now
        Last7Days -> subtractDays 7 now
        AllTime -> bottom  -- Include all
  in filter (\p -> p.timestamp >= cutoff) points

-- Aggregate data points for display
aggregateForDisplay :: TimeRange -> Array UsageDataPoint -> Array AggregatedPoint
aggregateForDisplay range points = case range of
  LastHour -> aggregateByMinute 5 points   -- 5-minute buckets
  Last24Hours -> aggregateByHour points    -- Hourly buckets
  Last7Days -> aggregateByDay points       -- Daily buckets
  AllTime -> aggregateByDay points         -- Daily buckets
```

### Totals Calculation

```purescript
calculateTotals :: Array UsageDataPoint -> Totals
calculateTotals points =
  let 
    prompt = sum $ map _.promptTokens points
    completion = sum $ map _.completionTokens points
  in
    { promptTokens: prompt
    , completionTokens: completion
    , totalTokens: prompt + completion
    , cost: sum $ map _.cost points
    }
```

---

## CSS Styling

```css
.token-chart {
  background: var(--color-bg-surface);
  border: 1px solid var(--color-border-subtle);
  border-radius: var(--card-border-radius);
  padding: var(--space-4);
}

.token-chart__header {
  display: flex;
  justify-content: space-between;
  align-items: center;
  margin-bottom: var(--space-4);
}

.token-chart__title {
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  font-weight: var(--font-weight-semibold);
  color: var(--color-text-primary);
  text-transform: uppercase;
  letter-spacing: var(--letter-spacing-wider);
}

.token-chart__container {
  height: 200px;
  margin-bottom: var(--space-3);
}

.token-chart__legend {
  display: flex;
  justify-content: center;
  gap: var(--space-6);
}

.legend-item {
  display: flex;
  align-items: center;
  gap: var(--space-2);
  font-family: var(--font-mono);
  font-size: var(--font-size-sm);
  color: var(--color-text-secondary);
}

.legend-color {
  width: 12px;
  height: 3px;
  border-radius: 2px;
}

.legend-item--prompt .legend-color {
  background: var(--color-primary);
}

.legend-item--completion .legend-color {
  background: var(--color-success);
}

/* Time range selector */
.time-range-selector {
  display: flex;
  gap: var(--space-1);
}

.time-range-btn {
  padding: var(--space-1) var(--space-2);
  background: transparent;
  border: 1px solid var(--color-border-subtle);
  border-radius: 4px;
  font-family: var(--font-mono);
  font-size: var(--font-size-xs);
  color: var(--color-text-tertiary);
  cursor: pointer;
  transition: all var(--transition-fast);
}

.time-range-btn:hover {
  color: var(--color-text-secondary);
  border-color: var(--color-border-default);
}

.time-range-btn--selected {
  background: var(--color-primary-dim);
  border-color: var(--color-primary);
  color: var(--color-primary);
}
```

---

## Related Specifications

- `50-DASHBOARD-LAYOUT.md` - Parent component
- `13-TOKEN-USAGE-METRICS.md` - Data source
- `47-THEMING.md` - Color tokens

---

*"Data visualization should inform, not decorate."*
