-- | Metrics Utilities Tests
-- | Unit and property tests for metrics calculation
module Test.Bridge.Utils.MetricsSpec where

import Prelude
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual, shouldBeTrue)
import Test.QuickCheck (quickCheck, (<?>))
import Test.QuickCheck.Arbitrary (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, chooseInt, chooseFloat, arrayOf, suchThat)
import Bridge.Utils.Metrics
  ( calculateAverageResponseTime
  , calculateCost
  , calculateConsumptionRate
  , calculateTimeToDepletion
  , aggregateMetrics
  )
import Bridge.State.Store (UsageMetrics)

-- | Arbitrary instance for non-negative numbers
newtype NonNegativeNumber = NonNegativeNumber Number
instance Arbitrary NonNegativeNumber where
  arbitrary = NonNegativeNumber <$> chooseFloat 0.0 1000.0

-- | Arbitrary instance for positive numbers
newtype PositiveNumber = PositiveNumber Number
instance Arbitrary PositiveNumber where
  arbitrary = PositiveNumber <$> chooseFloat 0.0001 1000.0

-- | Test average response time calculation
testAverageResponseTime :: forall m. Monad m => m Unit
testAverageResponseTime = do
  describe "Average Response Time" do
    it "calculates average for non-empty array" do
      calculateAverageResponseTime [100.0, 200.0, 300.0] `shouldEqual` 200.0
      calculateAverageResponseTime [10.0, 20.0, 30.0, 40.0] `shouldEqual` 25.0
      calculateAverageResponseTime [1.0, 2.0, 3.0, 4.0, 5.0] `shouldEqual` 3.0
    
    it "returns zero for empty array" do
      calculateAverageResponseTime [] `shouldEqual` 0.0
    
    it "handles single value" do
      calculateAverageResponseTime [42.0] `shouldEqual` 42.0
      calculateAverageResponseTime [0.0] `shouldEqual` 0.0
      calculateAverageResponseTime [1000.0] `shouldEqual` 1000.0
    
    it "handles identical values" do
      calculateAverageResponseTime [50.0, 50.0, 50.0] `shouldEqual` 50.0
      calculateAverageResponseTime [100.0, 100.0, 100.0, 100.0] `shouldEqual` 100.0
    
    it "handles negative values" do
      -- Should handle gracefully (though negative times are invalid)
      calculateAverageResponseTime [-100.0, 200.0] `shouldEqual` 50.0
      calculateAverageResponseTime [-50.0, 0.0, 50.0] `shouldEqual` 0.0
    
    it "handles very large values" do
      calculateAverageResponseTime [1.0e10, 2.0e10, 3.0e10] `shouldEqual` 2.0e10
      calculateAverageResponseTime [1.0e15, 1.0e15] `shouldEqual` 1.0e15
    
    it "handles very small values" do
      calculateAverageResponseTime [0.000001, 0.000002, 0.000003] `shouldEqual` 0.000002
      calculateAverageResponseTime [1.0e-10, 2.0e-10] `shouldEqual` 1.5e-10
    
    it "handles mixed positive and negative" do
      calculateAverageResponseTime [-100.0, 0.0, 100.0, 200.0] `shouldEqual` 50.0
    
    it "handles floating point precision" do
      calculateAverageResponseTime [0.1, 0.2, 0.3] `shouldEqual` 0.2
      calculateAverageResponseTime [1.0 / 3.0, 2.0 / 3.0, 3.0 / 3.0] `shouldEqual` 2.0 / 3.0

-- | Property: Average is always within min and max (inclusive)
prop_averageInRange :: Array Number -> Boolean
prop_averageInRange times =
  if length times > 0 then
    let avg = calculateAverageResponseTime times
        minVal = foldl (\acc x -> if x < acc then x else acc) (head times) times
        maxVal = foldl (\acc x -> if x > acc then x else acc) (head times) times
    in avg >= minVal && avg <= maxVal
  else
    calculateAverageResponseTime times == 0.0

-- | Property: Average is sum divided by count (mathematical correctness)
prop_averageIsSumDividedByCount :: Array Number -> Boolean
prop_averageIsSumDividedByCount times =
  if length times > 0 then
    let avg = calculateAverageResponseTime times
        sum = foldl (+) 0.0 times
        count = fromInt (length times)
        expected = sum / count
        -- Allow for floating point precision errors
        diff = if avg > expected then avg - expected else expected - avg
    in diff < 0.0000001 -- Very small epsilon for floating point comparison
  else
    calculateAverageResponseTime times == 0.0

-- | Property: Average of single element equals that element
prop_averageOfSingleElement :: Number -> Boolean
prop_averageOfSingleElement n =
  calculateAverageResponseTime [n] == n

-- | Property: Average is linear (avg(a + b) = avg(a) + avg(b) for same-length arrays)
prop_averageIsLinear :: Array Number -> Array Number -> Boolean
prop_averageIsLinear times1 times2 =
  if length times1 == length times2 && length times1 > 0 then
    let avg1 = calculateAverageResponseTime times1
        avg2 = calculateAverageResponseTime times2
        combined = zipWith (+) times1 times2
        avgCombined = calculateAverageResponseTime combined
        expected = avg1 + avg2
        diff = if avgCombined > expected then avgCombined - expected else expected - avgCombined
    in diff < 0.0000001
  else
    true

foreign import zipWith :: (Number -> Number -> Number) -> Array Number -> Array Number -> Array Number

-- | Test cost calculation
testCost :: forall m. Monad m => m Unit
testCost = do
  describe "Cost Calculation" do
    it "calculates cost correctly" do
      calculateCost 1000 500 0.001 0.002 `shouldEqual` 2.0
    
    it "handles zero tokens" do
      calculateCost 0 0 0.001 0.002 `shouldEqual` 0.0
    
    it "handles different input/output costs" do
      calculateCost 100 200 0.01 0.02 `shouldEqual` 5.0

-- | Property: Cost is always non-negative
prop_costNonNegative :: Int -> Int -> Number -> Number -> Boolean
prop_costNonNegative promptTokens completionTokens inputCost outputCost =
  calculateCost promptTokens completionTokens inputCost outputCost >= 0.0

-- | Property: Cost is linear in tokens (cost(2*tokens) = 2*cost(tokens))
prop_costIsLinearInTokens :: Int -> Int -> Number -> Number -> Boolean
prop_costIsLinearInTokens promptTokens completionTokens inputCost outputCost =
  let cost1 = calculateCost promptTokens completionTokens inputCost outputCost
      cost2 = calculateCost (promptTokens * 2) (completionTokens * 2) inputCost outputCost
      expected = cost1 * 2.0
      diff = if cost2 > expected then cost2 - expected else expected - cost2
  in diff < 0.0000001

-- | Property: Cost is linear in rates (cost(tokens, 2*rate) = 2*cost(tokens, rate))
prop_costIsLinearInRates :: Int -> Int -> Number -> Number -> Boolean
prop_costIsLinearInRates promptTokens completionTokens inputCost outputCost =
  let cost1 = calculateCost promptTokens completionTokens inputCost outputCost
      cost2 = calculateCost promptTokens completionTokens (inputCost * 2.0) (outputCost * 2.0)
      expected = cost1 * 2.0
      diff = if cost2 > expected then cost2 - expected else expected - cost2
  in diff < 0.0000001

-- | Property: Cost with zero tokens is zero
prop_costWithZeroTokensIsZero :: Number -> Number -> Boolean
prop_costWithZeroTokensIsZero inputCost outputCost =
  calculateCost 0 0 inputCost outputCost == 0.0

-- | Property: Cost is additive (cost(p1+c1, p2+c2) = cost(p1, c1) + cost(p2, c2))
prop_costIsAdditive :: Int -> Int -> Int -> Int -> Number -> Number -> Boolean
prop_costIsAdditive p1 c1 p2 c2 inputCost outputCost =
  let cost1 = calculateCost p1 c1 inputCost outputCost
      cost2 = calculateCost p2 c2 inputCost outputCost
      costCombined = calculateCost (p1 + p2) (c1 + c2) inputCost outputCost
      expected = cost1 + cost2
      diff = if costCombined > expected then costCombined - expected else expected - costCombined
  in diff < 0.0000001

-- | Test consumption rate calculation
testConsumptionRate :: forall m. Monad m => m Unit
testConsumptionRate = do
  describe "Consumption Rate" do
    it "calculates consumption rate correctly" do
      calculateConsumptionRate 1000 10.0 `shouldEqual` 100.0
    
    it "returns zero for zero duration" do
      calculateConsumptionRate 1000 0.0 `shouldEqual` 0.0
    
    it "returns zero for negative duration" do
      calculateConsumptionRate 1000 (-10.0) `shouldEqual` 0.0
    
    it "handles zero tokens" do
      calculateConsumptionRate 0 10.0 `shouldEqual` 0.0

-- | Property: Consumption rate is always non-negative
prop_consumptionRateNonNegative :: Int -> Number -> Boolean
prop_consumptionRateNonNegative tokens duration =
  calculateConsumptionRate tokens duration >= 0.0

-- | Test time to depletion calculation
testTimeToDepletion :: forall m. Monad m => m Unit
testTimeToDepletion = do
  describe "Time To Depletion" do
    it "calculates time to depletion correctly" do
      case calculateTimeToDepletion 1000.0 10.0 of
        Just time -> time `shouldEqual` 100.0
        Nothing -> false `shouldEqual` true
    
    it "returns Nothing for zero consumption rate" do
      case calculateTimeToDepletion 1000.0 0.0 of
        Just _ -> false `shouldEqual` true
        Nothing -> true `shouldEqual` true
    
    it "returns Nothing for negative consumption rate" do
      case calculateTimeToDepletion 1000.0 (-10.0) of
        Just _ -> false `shouldEqual` true
        Nothing -> true `shouldEqual` true
    
    it "handles zero balance" do
      case calculateTimeToDepletion 0.0 10.0 of
        Just time -> time `shouldEqual` 0.0
        Nothing -> false `shouldEqual` true

-- | Property: Time to depletion is always non-negative when Just
prop_timeToDepletionNonNegative :: PositiveNumber -> PositiveNumber -> Boolean
prop_timeToDepletionNonNegative (PositiveNumber balance) (PositiveNumber rate) =
  case calculateTimeToDepletion balance rate of
    Just time -> time >= 0.0
    Nothing -> false

-- | Test metrics aggregation
testAggregateMetrics :: forall m. Monad m => m Unit
testAggregateMetrics = do
  describe "Metrics Aggregation" do
    it "aggregates metrics correctly" do
      let metrics1 = { totalTokens: 100, totalCost: 1.0, averageResponseTime: 100.0, toolTimings: [] }
      let metrics2 = { totalTokens: 200, totalCost: 2.0, averageResponseTime: 200.0, toolTimings: [] }
      let aggregated = aggregateMetrics [metrics1, metrics2]
      aggregated.totalTokens `shouldEqual` 300
      aggregated.totalCost `shouldEqual` 3.0
    
    it "handles empty array" do
      let aggregated = aggregateMetrics []
      aggregated.totalTokens `shouldEqual` 0
      aggregated.totalCost `shouldEqual` 0.0
    
    it "aggregates tool timings" do
      let metrics1 = { totalTokens: 100, totalCost: 1.0, averageResponseTime: 100.0, toolTimings: ["tool1"] }
      let metrics2 = { totalTokens: 200, totalCost: 2.0, averageResponseTime: 200.0, toolTimings: ["tool2"] }
      let aggregated = aggregateMetrics [metrics1, metrics2]
      length aggregated.toolTimings `shouldEqual` 2

-- | Property: Aggregated total tokens equals sum
prop_aggregatedTokensEqualSum :: Array UsageMetrics -> Boolean
prop_aggregatedTokensEqualSum metrics =
  let aggregated = aggregateMetrics metrics
      expectedSum = foldl (\acc m -> acc + m.totalTokens) 0 metrics
  in aggregated.totalTokens == expectedSum

-- | Property: Aggregated total cost equals sum
prop_aggregatedCostEqualSum :: Array UsageMetrics -> Boolean
prop_aggregatedCostEqualSum metrics =
  let aggregated = aggregateMetrics metrics
      expectedSum = foldl (\acc m -> acc + m.totalCost) 0.0 metrics
  in aggregated.totalCost == expectedSum

-- | Property: Consumption rate is proportional to tokens
prop_consumptionRateProportional :: Int -> Number -> Boolean
prop_consumptionRateProportional tokens duration =
  if duration > 0.0 && tokens >= 0 then
    let rate1 = calculateConsumptionRate tokens duration
        rate2 = calculateConsumptionRate (tokens * 2) duration
        expected = rate1 * 2.0
        diff = if rate2 > expected then rate2 - expected else expected - rate2
    in diff < 0.0000001
  else
    true

-- | Property: Consumption rate is inversely proportional to duration
prop_consumptionRateInverseDuration :: Int -> Number -> Boolean
prop_consumptionRateInverseDuration tokens duration =
  if duration > 0.0 && tokens >= 0 then
    let rate1 = calculateConsumptionRate tokens duration
        rate2 = calculateConsumptionRate tokens (duration * 2.0)
        expected = rate1 / 2.0
        diff = if rate2 > expected then rate2 - expected else expected - rate2
    in diff < 0.0000001
  else
    true

-- | Property: Time to depletion is consistent with consumption rate
prop_timeToDepletionConsistent :: PositiveNumber -> PositiveNumber -> Boolean
prop_timeToDepletionConsistent (PositiveNumber balance) (PositiveNumber rate) =
  case calculateTimeToDepletion balance rate of
    Just time ->
      let expectedConsumption = time * rate
          diff = if balance > expectedConsumption then balance - expectedConsumption else expectedConsumption - balance
      in diff < 0.0000001 -- Allow for floating point precision
    Nothing -> false

-- | Property: Aggregation preserves individual metrics
prop_aggregationPreservesMetrics :: Array UsageMetrics -> Boolean
prop_aggregationPreservesMetrics metrics =
  if length metrics > 0 then
    let aggregated = aggregateMetrics metrics
        -- Check that aggregated values are at least as large as any individual metric
        allTokensValid = all (\m -> aggregated.totalTokens >= m.totalTokens) metrics
        allCostsValid = all (\m -> aggregated.totalCost >= m.totalCost) metrics
    in allTokensValid && allCostsValid
  else
    let aggregated = aggregateMetrics metrics
    in aggregated.totalTokens == 0 && aggregated.totalCost == 0.0

foreign import all :: forall a. (a -> Boolean) -> Array a -> Boolean

-- | Property tests
testProperties :: forall m. Monad m => m Unit
testProperties = do
  describe "Property Tests" do
    it "average is always in range" do
      quickCheck prop_averageInRange
    
    it "average is sum divided by count" do
      quickCheck prop_averageIsSumDividedByCount
    
    it "average of single element equals that element" do
      quickCheck prop_averageOfSingleElement
    
    it "average is linear" do
      quickCheck prop_averageIsLinear
    
    it "cost is always non-negative" do
      quickCheck prop_costNonNegative
    
    it "cost is linear in tokens" do
      quickCheck prop_costIsLinearInTokens
    
    it "cost is linear in rates" do
      quickCheck prop_costIsLinearInRates
    
    it "cost with zero tokens is zero" do
      quickCheck prop_costWithZeroTokensIsZero
    
    it "cost is additive" do
      quickCheck prop_costIsAdditive
    
    it "consumption rate is always non-negative" do
      quickCheck prop_consumptionRateNonNegative
    
    it "consumption rate is proportional to tokens" do
      quickCheck prop_consumptionRateProportional
    
    it "consumption rate is inversely proportional to duration" do
      quickCheck prop_consumptionRateInverseDuration
    
    it "time to depletion is always non-negative when Just" do
      quickCheck prop_timeToDepletionNonNegative
    
    it "time to depletion is consistent with consumption rate" do
      quickCheck prop_timeToDepletionConsistent
    
    it "aggregated tokens equal sum" do
      quickCheck prop_aggregatedTokensEqualSum
    
    it "aggregated cost equals sum" do
      quickCheck prop_aggregatedCostEqualSum
    
    it "aggregation preserves individual metrics" do
      quickCheck prop_aggregationPreservesMetrics

foreign import length :: forall a. Array a -> Int
foreign import foldl :: forall a b. (b -> a -> b) -> b -> Array a -> b
foreign import head :: forall a. Array a -> a
foreign import min :: Number -> Number -> Number
foreign import max :: Number -> Number -> Number
