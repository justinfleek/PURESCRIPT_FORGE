-- | Cost Projection - Forecasting and Budget Management
-- |
-- | **What:** Provides algorithms for forecasting Diem consumption, calculating time to
-- |         depletion, estimating message costs, and generating usage scenarios.
-- | **Why:** Helps users understand when they'll run out of Diem, estimate costs before
-- |         sending messages, and plan usage based on different scenarios.
-- | **How:** Uses consumption rate and balance history to project future consumption,
-- |         calculates depletion times, and estimates costs based on message content and
-- |         model pricing.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.FFI.DateTime`: DateTime operations
-- | - `Sidepanel.State.BalanceMetrics`: BalanceSnapshot type
-- |
-- | **Mathematical Foundation:**
-- | - **Time to Depletion:** `hours = currentBalance / consumptionRate`
-- | - **Balance at Reset:** `balanceAtReset = currentBalance - (rate * hoursToReset)`
-- | - **Cost Estimation:** `cost = (inputTokens / 1000 * inputPrice) + (outputTokens / 1000 * outputPrice)`
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Projection as Projection
-- |
-- | -- Calculate depletion prediction
-- | prediction = Projection.calculateTimeToDepletion 42.5 5.2 resetTime
-- |
-- | -- Estimate message cost
-- | estimate = Projection.estimateMessageCost message context "gpt-4" SimpleQuestion
-- | ```
-- |
-- | Based on spec 15-COST-PROJECTION.md
module Sidepanel.Projection where

import Prelude
import Data.DateTime (DateTime)
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Data.Int as Int
import Data.String as String
import Sidepanel.State.BalanceMetrics (BalanceSnapshot)
import Sidepanel.FFI.DateTime (toTimestamp, fromTimestamp)
import Math (max)

-- | Depletion prediction - Projection of when balance will deplete
-- |
-- | **Purpose:** Represents a prediction of when balance will reach zero and whether
-- |             it will make it to the reset time.
-- | **Fields:**
-- | - `willDeplete`: Whether balance will deplete before reset
-- | - `hoursRemaining`: Hours until balance reaches zero
-- | - `depletionTime`: When balance will reach zero (if willDeplete)
-- | - `willMakeItToReset`: Whether balance will last until reset time
-- | - `balanceAtReset`: Projected balance at reset time
type DepletionPrediction =
  { willDeplete :: Boolean
  , hoursRemaining :: Number
  , depletionTime :: Maybe DateTime
  , willMakeItToReset :: Boolean
  , balanceAtReset :: Number
  }

-- | Cost estimate - Estimated cost for a message
-- |
-- | **Purpose:** Represents an estimated cost for sending a message based on input/output
-- |             token estimates and model pricing.
-- | **Fields:**
-- | - `inputTokens`: Estimated input tokens
-- | - `outputTokens`: Estimated output tokens
-- | - `totalTokens`: Total estimated tokens
-- | - `estimatedCost`: Estimated cost in Diem/USD
-- | - `confidence`: Confidence level of estimate
data Confidence = High | Medium | Low

derive instance eqConfidence :: Eq Confidence

type CostEstimate =
  { inputTokens :: Int
  , outputTokens :: Int
  , totalTokens :: Int
  , estimatedCost :: Number
  , confidence :: Confidence
  }

-- | Query type - Type of query for output estimation
-- |
-- | **Purpose:** Different query types have different output token multipliers.
data QueryType
  = SimpleQuestion      -- Short answer (0.3x input)
  | Explanation         -- Medium explanation (0.8x input)
  | CodeGeneration      -- Code is verbose (1.5x input)
  | Debugging           -- Analysis + fix (1.2x input)
  | Refactoring         -- Large code blocks (2.0x input)

derive instance eqQueryType :: Eq QueryType

-- | Scenario - Usage scenario with projection
-- |
-- | **Purpose:** Represents a usage scenario (light/current/heavy) with its projection.
type Scenario =
  { name :: String
  , rate :: Number  -- Diem per hour
  , prediction :: DepletionPrediction
  }

-- | Calculate time to depletion - Project when balance will reach zero
-- |
-- | **Purpose:** Calculates when balance will deplete at a given consumption rate,
-- |             and whether it will make it to reset time.
-- | **Parameters:**
-- | - `currentBalance`: Current Diem balance
-- | - `consumptionRate`: Consumption rate in Diem per hour
-- | - `resetTime`: When Diem resets (UTC midnight)
-- | - `currentTime`: Current DateTime
-- | **Returns:** DepletionPrediction with all projection details
-- | **Side Effects:** None (pure function)
-- |
-- | **Algorithm:**
-- | 1. If rate <= 0: Will not deplete, balance stays same
-- | 2. Calculate hours to depletion: `hours = balance / rate`
-- | 3. Calculate hours to reset: `hoursToReset = (resetTime - currentTime) / 3600000`
-- | 4. Compare: If hoursToDepletion > hoursToReset, will make it to reset
-- | 5. Calculate balance at reset: `balance - (rate * hoursToReset)`
calculateTimeToDepletion :: Number -> Number -> DateTime -> DateTime -> DepletionPrediction
calculateTimeToDepletion currentBalance consumptionRate resetTime currentTime
  | consumptionRate <= 0.0 =
      { willDeplete: false
      , hoursRemaining: 999999.0  -- Effectively infinite
      , depletionTime: Nothing
      , willMakeItToReset: true
      , balanceAtReset: currentBalance
      }
  | currentBalance <= 0.0 =
      { willDeplete: true
      , hoursRemaining: 0.0
      , depletionTime: Just currentTime
      , willMakeItToReset: false
      , balanceAtReset: 0.0
      }
  | otherwise =
      let
        hoursToDepletion = currentBalance / consumptionRate
        depletionTimestamp = toTimestamp currentTime + (hoursToDepletion * 3600.0 * 1000.0)
        depletionTime = fromTimestamp depletionTimestamp
        
        hoursToReset = (toTimestamp resetTime - toTimestamp currentTime) / (3600.0 * 1000.0)
        willMakeItToReset = hoursToDepletion > hoursToReset
        balanceAtReset = if willMakeItToReset
          then max 0.0 (currentBalance - (consumptionRate * hoursToReset))
          else 0.0
      in
        { willDeplete: true
        , hoursRemaining: hoursToDepletion
        , depletionTime: Just depletionTime
        , willMakeItToReset
        , balanceAtReset
        }

-- | Estimate message cost - Estimate cost for sending a message
-- |
-- | **Purpose:** Estimates the cost of sending a message based on content length,
-- |             context size, model, and query type.
-- | **Parameters:**
-- | - `message`: Message content text
-- | - `contextTokens`: Total tokens in context (files, history, etc.)
-- | - `model`: Model name (for pricing lookup)
-- | - `queryType`: Type of query (affects output token multiplier)
-- | **Returns:** CostEstimate with token counts and cost
-- | **Side Effects:** None (pure function)
-- |
-- | **Algorithm:**
-- | 1. Estimate input tokens: `messageTokens + contextTokens + systemPromptTokens`
-- | 2. Estimate output tokens: `inputTokens * outputMultiplier[queryType]`
-- | 3. Get model pricing (simplified - would lookup from pricing table)
-- | 4. Calculate cost: `(inputTokens / 1000 * inputPrice) + (outputTokens / 1000 * outputPrice)`
-- | 5. Determine confidence based on context size
estimateMessageCost :: String -> Int -> String -> QueryType -> CostEstimate
estimateMessageCost message contextTokens model queryType =
  let
    messageTokens = estimateTokens message
    systemPromptTokens = 500  -- Approximate system prompt size
    inputTokens = messageTokens + contextTokens + systemPromptTokens
    
    outputMultiplier = case queryType of
      SimpleQuestion -> 0.3
      Explanation -> 0.8
      CodeGeneration -> 1.5
      Debugging -> 1.2
      Refactoring -> 2.0
    
    outputTokens = round (Int.toNumber inputTokens * outputMultiplier)
    totalTokens = inputTokens + outputTokens
    
    -- Simplified pricing (would lookup from pricing table)
    pricing = getModelPricing model
    estimatedCost = (Int.toNumber inputTokens / 1000.0 * pricing.inputPer1K) +
                    (Int.toNumber outputTokens / 1000.0 * pricing.outputPer1K)
    
    confidence = if contextTokens < 1000 then High
                 else if contextTokens < 5000 then Medium
                 else Low
  in
    { inputTokens
    , outputTokens
    , totalTokens
    , estimatedCost
    , confidence
    }

-- | Estimate tokens from text - Rough token estimation
-- |
-- | **Purpose:** Estimates token count from text content (rough approximation).
-- | **Algorithm:** 1 token ≈ 4 characters
estimateTokens :: String -> Int
estimateTokens text = round (Int.toNumber (String.length text) / 4.0)

-- | Model pricing - Pricing per 1K tokens
type ModelPricing =
  { inputPer1K :: Number
  , outputPer1K :: Number
  }

-- | Get model pricing - Lookup pricing for a model
-- |
-- | **Purpose:** Returns pricing information for a model (simplified - would lookup
-- |             from pricing table in production).
getModelPricing :: String -> ModelPricing
getModelPricing model = case model of
  "gpt-4" -> { inputPer1K: 0.03, outputPer1K: 0.06 }
  "gpt-4-turbo" -> { inputPer1K: 0.01, outputPer1K: 0.03 }
  "gpt-3.5-turbo" -> { inputPer1K: 0.0015, outputPer1K: 0.002 }
  "llama-3.3-70b" -> { inputPer1K: 0.0007, outputPer1K: 0.0007 }
  _ -> { inputPer1K: 0.001, outputPer1K: 0.002 }  -- Default

-- | Generate scenarios - Generate usage scenarios with projections
-- |
-- | **Purpose:** Generates three scenarios (light, current, heavy) with their projections.
-- | **Parameters:**
-- | - `currentBalance`: Current Diem balance
-- | - `currentRate`: Current consumption rate
-- | - `resetTime`: When Diem resets
-- | - `currentTime`: Current DateTime
-- | **Returns:** Array of scenarios with projections
generateScenarios :: Number -> Number -> DateTime -> DateTime -> Array Scenario
generateScenarios currentBalance currentRate resetTime currentTime =
  let
    rates =
      [ { name: "Light usage", factor: 0.5 }
      , { name: "Current pace", factor: 1.0 }
      , { name: "Heavy usage", factor: 1.5 }
      ]
  in
    Array.map (\{ name, factor } ->
      { name
      , rate: currentRate * factor
      , prediction: calculateTimeToDepletion currentBalance (currentRate * factor) resetTime currentTime
      }
    ) rates
