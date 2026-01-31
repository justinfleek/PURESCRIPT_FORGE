-- | Recharts FFI Module - Chart Visualization Bindings
-- |
-- | **What:** Provides FFI bindings for Recharts library, enabling token usage chart
-- |         visualization in PureScript components.
-- | **Why:** Enables rich data visualization (line charts) for token usage trends, helping
-- |         users understand consumption patterns over time.
-- | **How:** Uses foreign function imports to create and manage Recharts chart instances,
-- |         update chart data, and configure chart appearance. Charts are rendered in DOM
-- |         elements identified by ID.
-- |
-- | **Dependencies:** None (pure FFI bindings, requires Recharts JavaScript library)
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.FFI.Recharts as Recharts
-- |
-- | -- Create chart
-- | chart <- liftEffect $ Recharts.createLineChart "element-id"
-- |   { width: 800, height: 400, showCost: true, showBreakdown: true }
-- |   dataPoints
-- |
-- | -- Update chart data
-- | liftEffect $ Recharts.updateChartData chart newDataPoints
-- |
-- | -- Dispose chart
-- | liftEffect $ Recharts.disposeChart chart
-- | ```
module Sidepanel.FFI.Recharts where

import Prelude
import Effect (Effect)
import Data.Array (Array)

-- | Chart data point
type ChartDataPoint =
  { timestamp :: Number
  , promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  , cost :: Number
  }

-- | Chart configuration
type ChartConfig =
  { width :: Int
  , height :: Int
  , showCost :: Boolean
  , showBreakdown :: Boolean
  }

-- | Opaque Chart type
foreign import data ChartInstance :: Type

-- | Create line chart in DOM element
foreign import createLineChart :: String -> ChartConfig -> Array ChartDataPoint -> Effect ChartInstance

-- | Update chart data
foreign import updateChartData :: ChartInstance -> Array ChartDataPoint -> Effect Unit

-- | Update chart config
foreign import updateChartConfig :: ChartInstance -> ChartConfig -> Effect Unit

-- | Dispose chart
foreign import disposeChart :: ChartInstance -> Effect Unit
