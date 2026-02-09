-- | Metrics Utilities
-- | Metrics calculation and aggregation
module Bridge.Utils.Metrics where

import Prelude
import Data.Array (foldl, length)
import Bridge.State.Store (UsageMetrics)

-- | Calculate average response time
calculateAverageResponseTime :: Array Number -> Number
calculateAverageResponseTime times = 
  if length times == 0 then
    0.0
  else
    foldl (+) 0.0 times / fromInt (length times)

-- | Calculate total cost from token usage
calculateCost :: Int -> Int -> Number -> Number -> Number
calculateCost promptTokens completionTokens inputCost outputCost =
  (fromInt promptTokens * inputCost) + (fromInt completionTokens * outputCost)

-- | Calculate consumption rate (tokens per second)
calculateConsumptionRate :: Int -> Number -> Number
calculateConsumptionRate tokens durationSeconds =
  if durationSeconds <= 0.0 then
    0.0
  else
    fromInt tokens / durationSeconds

-- | Calculate time to depletion
calculateTimeToDepletion :: Number -> Number -> Maybe Number
calculateTimeToDepletion balance consumptionRate =
  if consumptionRate <= 0.0 then
    Nothing
  else
    Just (balance / consumptionRate)

-- | Aggregate metrics from multiple sources
aggregateMetrics :: Array UsageMetrics -> UsageMetrics
aggregateMetrics metricsArray =
  { totalTokens: foldl (\acc m -> acc + m.totalTokens) 0 metricsArray
  , totalCost: foldl (\acc m -> acc + m.totalCost) 0.0 metricsArray
  , averageResponseTime: calculateAverageResponseTime (map _.averageResponseTime metricsArray)
  , toolTimings: foldl (\acc m -> acc <> m.toolTimings) [] metricsArray
  }

foreign import fromInt :: Int -> Number
