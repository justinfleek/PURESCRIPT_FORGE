-- | Metrics Calculation Utilities
module Bridge.Utils.Metrics where

import Prelude
import Data.Array (foldl, length)
import Data.Maybe (Maybe(..))
import Bridge.State.Store.Types (UsageMetrics)

-- | FFI for Int to Number conversion
foreign import fromInt :: Int -> Number

-- | Calculate average response time from an array of times
calculateAverageResponseTime :: Array Number -> Number
calculateAverageResponseTime times =
  let len = length times
  in if len == 0 then 0.0
     else foldl (+) 0.0 times / fromInt len

-- | Calculate cost from token counts and rates
calculateCost :: Int -> Int -> Number -> Number -> Number
calculateCost promptTokens completionTokens inputCost outputCost =
  (fromInt promptTokens * inputCost) + (fromInt completionTokens * outputCost)

-- | Calculate token consumption rate (tokens per second)
calculateConsumptionRate :: Int -> Number -> Number
calculateConsumptionRate tokens duration =
  if duration <= 0.0 then 0.0
  else fromInt tokens / duration

-- | Calculate time to balance depletion
calculateTimeToDepletion :: Number -> Number -> Maybe Number
calculateTimeToDepletion balance rate =
  if rate <= 0.0 then Nothing
  else Just (balance / rate)

-- | Aggregate multiple metrics records
aggregateMetrics :: Array UsageMetrics -> UsageMetrics
aggregateMetrics metrics =
  let summed = foldl accumulate emptyMetrics metrics
      len = length metrics
      avgTime = if len == 0 then 0.0
                else summed.averageResponseTime / fromInt len
  in summed { averageResponseTime = avgTime }
  where
    emptyMetrics :: UsageMetrics
    emptyMetrics =
      { totalTokens: 0
      , totalCost: 0.0
      , averageResponseTime: 0.0
      , toolTimings: []
      }

    accumulate :: UsageMetrics -> UsageMetrics -> UsageMetrics
    accumulate acc m =
      { totalTokens: acc.totalTokens + m.totalTokens
      , totalCost: acc.totalCost + m.totalCost
      , averageResponseTime: acc.averageResponseTime + m.averageResponseTime
      , toolTimings: acc.toolTimings <> m.toolTimings
      }
