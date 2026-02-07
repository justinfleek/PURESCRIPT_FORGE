-- | Property Tests for Token Usage Utilities with Realistic Distributions
-- |
-- | Based on spec 70-TESTING-STRATEGY.md and 71-UNIT-TESTING.md
-- | Tests token usage utilities with realistic data distributions
-- |
-- | Reference: REQUIRED/trtllm-serve-main/nix/openai-proxy-hs/ProxyPropTest.hs
module Test.Sidepanel.Property.TokenUsageProps where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.QuickCheck (quickCheck)
import Test.QuickCheck (class Arbitrary, arbitrary, (===), (==>))
import Test.QuickCheck.Gen (Gen, chooseInt, chooseFloat, arrayOf, elements, frequency)
import Data.Array as Array
import Data.Foldable (sum)
import Data.DateTime (DateTime)
import Data.Maybe (fromMaybe)
import Sidepanel.Utils.TokenUsage as TokenUsage
import Sidepanel.State.AppState (SessionSummary)
import Sidepanel.FFI.DateTime (fromTimestamp, toTimestamp)
import Test.Sidepanel.TestFixtures (testDateTime)

-- | Arbitrary instance for SessionSummary with realistic distributions
instance arbitrarySessionSummary :: Arbitrary SessionSummary where
  arbitrary = do
    -- Generate realistic session ID
    idNum <- chooseInt 1 10000
    let id = "session-" <> show idNum
    
    -- Model distribution: 60% gpt-4, 30% gpt-3.5, 10% others
    model <- frequency
      [ (60.0, elements ["gpt-4", "gpt-4-turbo", "gpt-4-32k"])
      , (30.0, elements ["gpt-3.5-turbo", "gpt-3.5-turbo-16k"])
      , (10.0, elements ["claude-3-opus", "claude-3-sonnet", "llama-3.3-70b"])
      ]
    
    -- Cost distribution: Normal-like distribution around $0.10
    cost <- normalLike 0.10 0.05 0.0 1.0
    
    -- Token count: Normal-like distribution around 2000 tokens
    tokenCount <- normalLike 2000.0 1000.0 100.0 10000.0
    
    -- Timestamp: Random timestamp within last 30 days
    daysAgo <- chooseFloat 0.0 30.0
    let timestamp = toTimestamp testDateTime - (daysAgo * 24.0 * 3600.0 * 1000.0)
    startedAt <- pure $ fromTimestamp timestamp
    
    pure { id, model, cost, tokenCount, startedAt }

-- | Generate normal-like distribution
-- | Uses simplified approach: generate values around mean with frequency
normalLike :: Number -> Number -> Number -> Number -> Gen Number
normalLike mean stdDev min max = do
  -- Simplified: use frequency to approximate normal distribution
  offset <- frequency
    [ (34.0, chooseFloat (-stdDev) 0.0)  -- 34% within 1 std dev below mean
    , (34.0, chooseFloat 0.0 stdDev)     -- 34% within 1 std dev above mean
    , (14.0, chooseFloat (-2.0 * stdDev) (-stdDev))  -- 14% between 1-2 std dev below
    , (14.0, chooseFloat stdDev (2.0 * stdDev))      -- 14% between 1-2 std dev above
    , (4.0, chooseFloat (-3.0 * stdDev) (-2.0 * stdDev))  -- 4% tail
    ]
  let value = mean + offset
  -- Clamp to bounds
  pure $ if value < min then min else if value > max then max else value

-- | Property: Cost breakdown percentages sum to 100%
prop_costBreakdownPercentagesSum :: Array SessionSummary -> Boolean
prop_costBreakdownPercentagesSum sessions =
  if Array.null sessions then true
  else
    let breakdown = TokenUsage.calculateCostBreakdown sessions
        totalPercentage = sum (Array.map _.percentage breakdown)
        -- Allow small floating point errors
        diff = abs (totalPercentage - 100.0)
    in diff < 0.01

-- | Property: Cost breakdown costs sum to total cost
prop_costBreakdownCostsSum :: Array SessionSummary -> Boolean
prop_costBreakdownCostsSum sessions =
  if Array.null sessions then true
  else
    let breakdown = TokenUsage.calculateCostBreakdown sessions
        totalCostFromBreakdown = sum (Array.map _.cost breakdown)
        totalCostFromSessions = sum (Array.map _.cost sessions)
        diff = abs (totalCostFromBreakdown - totalCostFromSessions)
    in diff < 0.0001  -- Allow small floating point errors

-- | Property: Cost breakdown is sorted by cost descending
prop_costBreakdownSorted :: Array SessionSummary -> Boolean
prop_costBreakdownSorted sessions =
  let breakdown = TokenUsage.calculateCostBreakdown sessions
      costs = Array.map _.cost breakdown
      isSorted = Array.allWithIndex (\i cost -> 
        if i == 0 then true
        else cost <= Array.index costs (i - 1) # fromMaybe cost
      ) costs
  in isSorted

-- | Property: All models from sessions appear in breakdown
prop_costBreakdownContainsAllModels :: Array SessionSummary -> Boolean
prop_costBreakdownContainsAllModels sessions =
  if Array.null sessions then true
  else
    let breakdown = TokenUsage.calculateCostBreakdown sessions
        breakdownModels = Array.map _.model breakdown
        sessionModels = Array.map _.model sessions
        -- Check that every session model appears in breakdown
        allPresent = Array.all (\model -> Array.elem model breakdownModels) sessionModels
    in allPresent

-- | Property: Time range filtering preserves order
prop_timeRangeFilteringPreservesOrder :: TokenUsage.TimeRange -> Array SessionSummary -> DateTime -> Boolean
prop_timeRangeFilteringPreservesOrder range sessions now =
  let filtered = TokenUsage.filterSessionsByTimeRange range sessions now
      -- Check that filtered sessions maintain relative order
      -- (if session A comes before B in original and both are in filtered, A comes before B)
      originalIndices = Array.mapWithIndex (\i s -> { index: i, session: s }) sessions
      filteredIndices = Array.mapWithIndex (\i s -> { index: i, session: s }) filtered
      -- For each filtered session, find its original index
      originalOrder = Array.mapMaybe (\{ index, session } ->
        Array.findIndex (\s -> s.id == session.id) sessions # map (\origIdx -> { filteredIdx: index, originalIdx: origIdx })
      ) filteredIndices
      -- Check that original indices are in ascending order
      isOrdered = Array.allWithIndex (\i { originalIdx } ->
        if i == 0 then true
        else originalIdx > (Array.index originalOrder (i - 1) # map _.originalIdx # fromMaybe (-1))
      ) originalOrder
  in isOrdered

-- | Property: AllTime range includes all sessions
prop_allTimeRangeIncludesAll :: Array SessionSummary -> DateTime -> Boolean
prop_allTimeRangeIncludesAll sessions now =
  let filtered = TokenUsage.filterSessionsByTimeRange TokenUsage.AllTime sessions now
  in Array.length filtered == Array.length sessions

-- | Property: Sessions to data points preserves count
prop_sessionsToDataPointsPreservesCount :: Array SessionSummary -> Boolean
prop_sessionsToDataPointsPreservesCount sessions =
  let dataPoints = TokenUsage.sessionsToDataPoints sessions
  in Array.length dataPoints == Array.length sessions

-- | Property: Sessions to data points preserves cost
prop_sessionsToDataPointsPreservesCost :: SessionSummary -> Boolean
prop_sessionsToDataPointsPreservesCost session =
  let dataPoints = TokenUsage.sessionsToDataPoints [session]
      point = Array.head dataPoints
  in case point of
    Just p -> abs (p.cost - session.cost) < 0.0001
    Nothing -> false

-- | Property: Sessions to data points preserves token count
prop_sessionsToDataPointsPreservesTokens :: SessionSummary -> Boolean
prop_sessionsToDataPointsPreservesTokens session =
  let dataPoints = TokenUsage.sessionsToDataPoints [session]
      point = Array.head dataPoints
  in case point of
    Just p -> p.totalTokens == session.tokenCount
    Nothing -> false

-- | Test suite
spec :: Spec Unit
spec = describe "Token Usage Property Tests" do
  describe "Cost Breakdown Properties" do
    it "percentages sum to 100%" do
      quickCheck prop_costBreakdownPercentagesSum
    
    it "costs sum to total cost" do
      quickCheck prop_costBreakdownCostsSum
    
    it "is sorted by cost descending" do
      quickCheck prop_costBreakdownSorted
    
    it "contains all models from sessions" do
      quickCheck prop_costBreakdownContainsAllModels
  
  describe "Time Range Filtering Properties" do
    it "preserves order" do
      quickCheck prop_timeRangeFilteringPreservesOrder
    
    it "AllTime range includes all sessions" do
      quickCheck prop_allTimeRangeIncludesAll
  
  describe "Sessions to Data Points Properties" do
    it "preserves count" do
      quickCheck prop_sessionsToDataPointsPreservesCount
    
    it "preserves cost" do
      quickCheck prop_sessionsToDataPointsPreservesCost
    
    it "preserves token count" do
      quickCheck prop_sessionsToDataPointsPreservesTokens
