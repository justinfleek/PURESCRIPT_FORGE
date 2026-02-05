-- | Token Usage Utilities - Token Usage Data Processing
-- |
-- | **What:** Provides utility functions for processing token usage data for charts
-- |         and aggregations. Converts session history into chart data points and
-- |         cost breakdowns.
-- | **Why:** Enables dashboard charts to display token usage trends and cost
-- |         breakdowns by aggregating data from session history.
-- | **How:** Processes session history arrays to create time-series data points
-- |         and model-based cost aggregations.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.State.AppState`: SessionSummary type
-- | - `Data.DateTime`: DateTime operations
-- | - `Data.Array`: Array operations
-- |
-- | **Mathematical Foundation:**
-- | - **Time Range Filtering:** Filters sessions by `startedAt` timestamp within
-- |   the specified time range.
-- | - **Cost Aggregation:** Groups sessions by model and sums costs, calculates
-- |   percentages relative to total cost.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Utils.TokenUsage as TokenUsage
-- |
-- | -- Filter sessions by time range
-- | filtered = TokenUsage.filterSessionsByTimeRange LastHour sessionHistory
-- |
-- | -- Generate chart data points
-- | dataPoints = TokenUsage.sessionsToDataPoints filtered
-- |
-- | -- Calculate cost breakdown
-- | breakdown = TokenUsage.calculateCostBreakdown sessionHistory
-- | ```
module Sidepanel.Utils.TokenUsage where

import Prelude
import Data.Array as Array
import Data.DateTime (DateTime)
import Data.Maybe (Maybe(..))
import Data.Foldable (sum)
import Sidepanel.State.AppState (SessionSummary)
import Sidepanel.Components.TokenUsageChart (TokenDataPoint)
import Sidepanel.Components.CostBreakdownChart (CostBreakdown)
import Sidepanel.FFI.DateTime (toTimestamp, fromTimestamp)

-- | Time range for filtering
data TimeRange = LastHour | LastDay | LastWeek | AllTime

derive instance eqTimeRange :: Eq TimeRange

-- | Filter sessions by time range
-- |
-- | **Purpose:** Filters session history to include only sessions within the
-- |             specified time range, relative to the current time.
-- | **Parameters:**
-- | - `range`: Time range to filter by
-- | - `sessions`: Array of session summaries to filter
-- | - `now`: Current datetime for comparison
-- | **Returns:** Filtered array of sessions
filterSessionsByTimeRange :: TimeRange -> Array SessionSummary -> DateTime -> Array SessionSummary
filterSessionsByTimeRange range sessions now =
  let
    cutoffTime = getCutoffTime range now
  in
    Array.filter (\s -> isAfterOrEqual s.startedAt cutoffTime) sessions

-- | Get cutoff time for time range
-- |
-- | **Purpose:** Calculates the cutoff datetime for a given time range by subtracting
-- |             the appropriate duration from the current time.
-- | **Parameters:**
-- | - `range`: Time range (LastHour, LastDay, LastWeek, AllTime)
-- | - `now`: Current datetime
-- | **Returns:** Cutoff datetime (sessions after this time are included)
getCutoffTime :: TimeRange -> DateTime -> DateTime
getCutoffTime range now = case range of
  LastHour -> subtractHours 1 now
  LastDay -> subtractHours 24 now
  LastWeek -> subtractHours (24 * 7) now
  AllTime -> earliestDateTime  -- Include all sessions

-- | Subtract hours from DateTime
-- |
-- | **Purpose:** Subtracts the specified number of hours from a DateTime.
-- | **Note:** Uses timestamp conversion for simplicity and accuracy.
subtractHours :: Int -> DateTime -> DateTime
subtractHours hours dt =
  let
    timestamp = toTimestamp dt
    hoursMs = toNumber hours * 3600000.0  -- Convert hours to milliseconds
    newTimestamp = timestamp - hoursMs
  in
    fromTimestamp newTimestamp

-- | Check if datetime is after or equal to cutoff
-- |
-- | **Purpose:** Compares two datetimes to determine if the first is after or
-- |             equal to the second by comparing timestamps.
-- | **Returns:** True if dt1 >= dt2, false otherwise
isAfterOrEqual :: DateTime -> DateTime -> Boolean
isAfterOrEqual dt1 dt2 =
  let
    ts1 = toTimestamp dt1
    ts2 = toTimestamp dt2
  in
    ts1 >= ts2

-- | Earliest possible DateTime (epoch 0)
-- |
-- | **Purpose:** Returns the earliest DateTime (January 1, 1970 00:00:00 UTC)
-- |             to use as cutoff for "AllTime" range.
earliestDateTime :: DateTime
earliestDateTime = fromTimestamp 0.0

-- | Convert sessions to chart data points
-- |
-- | **Purpose:** Converts session summaries into token usage chart data points.
-- |             Each session becomes one data point with its token counts and cost.
-- | **Parameters:**
-- | - `sessions`: Array of session summaries
-- | **Returns:** Array of token data points
-- | **Note:** This creates one point per session. For smoother charts, sessions
-- |          could be aggregated into time buckets (hourly, daily, etc.).
sessionsToDataPoints :: Array SessionSummary -> Array TokenDataPoint
sessionsToDataPoints sessions =
  Array.map sessionToDataPoint sessions

-- | Convert single session to data point
sessionToDataPoint :: SessionSummary -> TokenDataPoint
sessionToDataPoint session =
  { timestamp: toTimestamp session.startedAt
  , promptTokens: session.tokenCount  -- TODO: Split into prompt/completion if available
  , completionTokens: 0  -- SessionSummary doesn't have separate prompt/completion
  , totalTokens: session.tokenCount
  , cost: session.cost
  }

-- | Calculate cost breakdown by model
-- |
-- | **Purpose:** Aggregates costs by model from session history, calculating
-- |             total cost per model and percentage of total cost.
-- | **Parameters:**
-- | - `sessions`: Array of session summaries
-- | **Returns:** Array of cost breakdowns, sorted by cost (descending)
calculateCostBreakdown :: Array SessionSummary -> Array CostBreakdown
calculateCostBreakdown sessions =
  let
    -- Group sessions by model and sum costs
    grouped = groupByModel sessions
    totalCost = sum (Array.map _.cost sessions)
    -- Convert to breakdown with percentages
    breakdowns = Array.map (\{ model, cost } ->
      { model
      , cost
      , percentage: if totalCost > 0.0 then (cost / totalCost) * 100.0 else 0.0
      }
    ) grouped
    -- Sort by cost descending
    sorted = Array.sortBy (\a b -> compare b.cost a.cost) breakdowns
  in
    sorted

-- | Group sessions by model and sum costs
-- |
-- | **Purpose:** Groups sessions by model name and calculates total cost per model.
-- | **Returns:** Array of model-cost pairs
groupByModel :: Array SessionSummary -> Array { model :: String, cost :: Number }
groupByModel sessions =
  let
    -- Create map of model -> total cost
    modelMap = Array.foldl
      (\acc session ->
        let
          existing = Array.find (\m -> m.model == session.model) acc
        in
          case existing of
            Just m -> Array.map (\x -> if x.model == session.model then { model: x.model, cost: x.cost + session.cost } else x) acc
            Nothing -> Array.snoc acc { model: session.model, cost: session.cost }
      )
      []
      sessions
  in
    modelMap
