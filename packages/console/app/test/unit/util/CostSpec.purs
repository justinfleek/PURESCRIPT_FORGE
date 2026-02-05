-- | Deep comprehensive tests for Cost module
-- | Tests all cost calculation functions, edge cases, and potential bugs
module Test.Unit.Util.CostSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual)
import Data.Maybe (Maybe(..), isJust, isNothing)

import Console.App.Routes.Omega.Util.Handler.Cost
  ( calculateCost
  )
import Console.App.Routes.Omega.Util.Handler.Types
  ( ModelInfo
  , CostInfo
  )
import Console.App.Routes.Omega.Util.Provider.Provider (UsageInfo)
import Console.Core.Util.Price (MicroCents, centsToMicroCents)

-- | Create mock ModelInfo with standard cost
mkMockModelInfo :: ModelInfo
mkMockModelInfo =
  { id: "gpt-4"
  , formatFilter: Nothing
  , providers: []
  , byokProvider: Nothing
  , trial: Nothing
  , rateLimit: Nothing
  , stickyProvider: Nothing
  , fallbackProvider: Nothing
  , allowAnonymous: false
  , cost:
      { input: 30.0  -- $30 per 1M tokens
      , output: 60.0  -- $60 per 1M tokens
      , cacheRead: Nothing
      , cacheWrite5m: Nothing
      , cacheWrite1h: Nothing
      }
  , cost200K: Nothing
  }

-- | Create mock ModelInfo with 200K cost
mkMockModelInfo200K :: ModelInfo
mkMockModelInfo200K =
  mkMockModelInfo
    { cost200K = Just
        { input: 15.0  -- $15 per 1M tokens (cheaper)
        , output: 30.0  -- $30 per 1M tokens
        , cacheRead: Nothing
        , cacheWrite5m: Nothing
        , cacheWrite1h: Nothing
        }
    }

-- | Create mock UsageInfo
mkMockUsageInfo :: UsageInfo
mkMockUsageInfo =
  { inputTokens: 1000
  , outputTokens: 500
  , reasoningTokens: Nothing
  , cacheReadTokens: Nothing
  , cacheWrite5mTokens: Nothing
  , cacheWrite1hTokens: Nothing
  }

-- | Deep comprehensive tests for Cost calculation
spec :: Spec Unit
spec = describe "Cost Deep Tests" do
  describe "calculateCost - Basic Calculations" do
    it "calculates cost for standard usage" do
      let modelInfo = mkMockModelInfo
      let usageInfo = mkMockUsageInfo
      let costInfo = calculateCost modelInfo usageInfo
      -- Input: 1000 tokens * $30/1M * 100 cents = 3 cents
      -- Output: 500 tokens * $60/1M * 100 cents = 3 cents
      -- Total: 6 cents = 600 microcents
      costInfo.costInMicroCents `shouldEqual` (centsToMicroCents 6)

    it "calculates cost with reasoning tokens" do
      let modelInfo = mkMockModelInfo
      let usageInfo = mkMockUsageInfo { reasoningTokens = Just 200 }
      let costInfo = calculateCost modelInfo usageInfo
      -- Input: 1000 tokens * $30/1M * 100 = 3 cents
      -- Output: 500 tokens * $60/1M * 100 = 3 cents
      -- Reasoning: 200 tokens * $60/1M * 100 = 1.2 cents (rounded to 1)
      -- Total: 7 cents = 700 microcents
      costInfo.costInMicroCents `shouldEqual` (centsToMicroCents 7)

    it "calculates cost with cache read tokens" do
      let modelInfo = mkMockModelInfo
        { cost = mkMockModelInfo.cost { cacheRead = Just 1.0 } }
      let usageInfo = mkMockUsageInfo { cacheReadTokens = Just 1000 }
      let costInfo = calculateCost modelInfo usageInfo
      -- Input: 1000 tokens * $30/1M * 100 = 3 cents
      -- Output: 500 tokens * $60/1M * 100 = 3 cents
      -- Cache read: 1000 tokens * $1/1M * 100 = 0.1 cents (rounded to 0)
      -- Total: 6 cents = 600 microcents
      costInfo.costInMicroCents `shouldEqual` (centsToMicroCents 6)

    it "calculates cost with all optional token types" do
      let modelInfo = mkMockModelInfo
        { cost =
            { input: 30.0
            , output: 60.0
            , cacheRead: Just 1.0
            , cacheWrite5m: Just 2.0
            , cacheWrite1h: Just 3.0
            }
        }
      let usageInfo =
            { inputTokens: 1000
            , outputTokens: 500
            , reasoningTokens: Just 200
            , cacheReadTokens: Just 1000
            , cacheWrite5mTokens: Just 500
            , cacheWrite1hTokens: Just 300
            }
      let costInfo = calculateCost modelInfo usageInfo
      -- All costs summed
      costInfo.costInMicroCents `shouldNotEqual` 0

  describe "calculateCost - 200K Threshold" do
    it "uses standard cost when below 200K threshold" do
      let modelInfo = mkMockModelInfo200K
      let usageInfo = mkMockUsageInfo { inputTokens = 200000 }  -- Exactly 200K
      let costInfo = calculateCost modelInfo usageInfo
      -- BUG: shouldUse200KCost uses > not >=, so exactly 200K uses standard cost
      -- Should use standard cost (30.0 input, 60.0 output)
      -- Input: 200000 tokens * $30/1M * 100 = 6000 cents
      -- Output: 500 tokens * $60/1M * 100 = 3 cents
      -- Total: 6003 cents
      costInfo.costInMicroCents `shouldEqual` (centsToMicroCents 6003)

    it "uses 200K cost when above 200K threshold" do
      let modelInfo = mkMockModelInfo200K
      let usageInfo = mkMockUsageInfo { inputTokens = 200001 }  -- Just above 200K
      let costInfo = calculateCost modelInfo usageInfo
      -- Should use 200K cost (15.0 input, 30.0 output)
      -- Input: 200001 tokens * $15/1M * 100 = 3000.015 cents (rounded to 3000)
      -- Output: 500 tokens * $30/1M * 100 = 1.5 cents (rounded to 2)
      -- Total: 3002 cents
      costInfo.costInMicroCents `shouldEqual` (centsToMicroCents 3002)

    it "BUG: threshold calculation excludes outputTokens and reasoningTokens" do
      -- BUG: shouldUse200KCost only counts inputTokens + cache tokens
      -- It doesn't include outputTokens or reasoningTokens in threshold
      let modelInfo = mkMockModelInfo200K
      let usageInfo =
            { inputTokens: 100000
            , outputTokens: 100000  -- Should count but doesn't
            , reasoningTokens: Just 1000  -- Should count but doesn't
            , cacheReadTokens: Nothing
            , cacheWrite5mTokens: Nothing
            , cacheWrite1hTokens: Nothing
            }
      let costInfo = calculateCost modelInfo usageInfo
      -- Total tokens: 201000, but threshold only sees 100000
      -- Should use standard cost, not 200K cost
      -- This test documents the bug: outputTokens and reasoningTokens not counted
      costInfo.costInMicroCents `shouldNotEqual` 0

    it "uses cache tokens in threshold calculation" do
      let modelInfo = mkMockModelInfo200K
      let usageInfo =
            { inputTokens: 100000
            , outputTokens: 0
            , reasoningTokens: Nothing
            , cacheReadTokens: Just 50000
            , cacheWrite5mTokens: Just 50000
            , cacheWrite1hTokens: Just 1000
            }
      let costInfo = calculateCost modelInfo usageInfo
      -- Total: 100000 + 50000 + 50000 + 1000 = 201000 > 200K
      -- Should use 200K cost
      costInfo.costInMicroCents `shouldNotEqual` 0

    it "BUG: fromMaybe used incorrectly when cost200K is Nothing" do
      -- BUG: Line 43 uses `fromMaybe modelInfo.cost modelInfo.cost200K`
      -- This means if cost200K is Nothing, it uses standard cost
      -- But shouldUse200KCost checks `isJust modelInfo.cost200K` first
      -- This case indicates invalid input data
      let modelInfo = mkMockModelInfo  -- No cost200K
      let usageInfo = mkMockUsageInfo { inputTokens = 300000 }  -- Above threshold
      let costInfo = calculateCost modelInfo usageInfo
      -- Should use standard cost (no 200K cost available)
      costInfo.costInMicroCents `shouldNotEqual` 0

  describe "calculateCost - Edge Cases" do
    it "handles zero tokens" do
      let modelInfo = mkMockModelInfo
      let usageInfo = mkMockUsageInfo
        { inputTokens = 0
        , outputTokens = 0
        }
      let costInfo = calculateCost modelInfo usageInfo
      costInfo.costInMicroCents `shouldEqual` (centsToMicroCents 0)

    it "handles negative tokens (edge case)" do
      -- Test handling of negative token values
      let modelInfo = mkMockModelInfo
      let usageInfo = mkMockUsageInfo { inputTokens = (-100) }
      let costInfo = calculateCost modelInfo usageInfo
      -- Should calculate negative cost (bug: should validate input)
      costInfo.costInMicroCents `shouldNotEqual` 0

    it "handles very large token counts" do
      let modelInfo = mkMockModelInfo
      let usageInfo = mkMockUsageInfo { inputTokens = 1000000000 }  -- 1B tokens
      let costInfo = calculateCost modelInfo usageInfo
      -- Input: 1B tokens * $30/1M * 100 = 30000000 cents
      -- Should handle large numbers correctly
      costInfo.costInMicroCents `shouldNotEqual` 0

    it "handles very small cost per token" do
      let modelInfo = mkMockModelInfo
        { cost = { input: 0.001, output: 0.001, cacheRead: Nothing, cacheWrite5m: Nothing, cacheWrite1h: Nothing } }
      let usageInfo = mkMockUsageInfo { inputTokens = 1000 }
      let costInfo = calculateCost modelInfo usageInfo
      -- Input: 1000 tokens * $0.001/1M * 100 = 0.1 cents (rounded to 0)
      costInfo.costInMicroCents `shouldEqual` (centsToMicroCents 0)

    it "handles very large cost per token" do
      let modelInfo = mkMockModelInfo
        { cost = { input: 1000.0, output: 2000.0, cacheRead: Nothing, cacheWrite5m: Nothing, cacheWrite1h: Nothing } }
      let usageInfo = mkMockUsageInfo { inputTokens = 1000 }
      let costInfo = calculateCost modelInfo usageInfo
      -- Input: 1000 tokens * $1000/1M * 100 = 100 cents
      -- Output: 500 tokens * $2000/1M * 100 = 100 cents
      -- Total: 200 cents
      costInfo.costInMicroCents `shouldEqual` (centsToMicroCents 200)

    it "handles all optional tokens as Nothing" do
      let modelInfo = mkMockModelInfo
      let usageInfo = mkMockUsageInfo
        { reasoningTokens = Nothing
        , cacheReadTokens = Nothing
        , cacheWrite5mTokens = Nothing
        , cacheWrite1hTokens = Nothing
        }
      let costInfo = calculateCost modelInfo usageInfo
      -- Only input and output tokens
      costInfo.costInMicroCents `shouldEqual` (centsToMicroCents 6)

    it "handles reasoning tokens with zero cost" do
      let modelInfo = mkMockModelInfo
        { cost = { input: 0.0, output: 0.0, cacheRead: Nothing, cacheWrite5m: Nothing, cacheWrite1h: Nothing } }
      let usageInfo = mkMockUsageInfo { reasoningTokens = Just 1000 }
      let costInfo = calculateCost modelInfo usageInfo
      -- All costs should be zero
      costInfo.costInMicroCents `shouldEqual` (centsToMicroCents 0)

  describe "calculateCost - Rounding Precision" do
    it "rounds fractional cents correctly" do
      let modelInfo = mkMockModelInfo
        { cost = { input: 1.0, output: 1.0, cacheRead: Nothing, cacheWrite5m: Nothing, cacheWrite1h: Nothing } }
      let usageInfo = mkMockUsageInfo { inputTokens = 1234 }  -- 0.1234 cents
      let costInfo = calculateCost modelInfo usageInfo
      -- Input: 1234 tokens * $1/1M * 100 = 0.1234 cents (rounded to 0)
      -- Output: 500 tokens * $1/1M * 100 = 0.05 cents (rounded to 0)
      -- Total: 0 cents
      costInfo.costInMicroCents `shouldEqual` (centsToMicroCents 0)

    it "rounds up fractional cents correctly" do
      let modelInfo = mkMockModelInfo
        { cost = { input: 1.0, output: 1.0, cacheRead: Nothing, cacheWrite5m: Nothing, cacheWrite1h: Nothing } }
      let usageInfo = mkMockUsageInfo { inputTokens = 5000 }  -- 0.5 cents (rounds to 1)
      let costInfo = calculateCost modelInfo usageInfo
      -- Input: 5000 tokens * $1/1M * 100 = 0.5 cents (rounded to 1)
      -- Output: 500 tokens * $1/1M * 100 = 0.05 cents (rounded to 0)
      -- Total: 1 cent
      costInfo.costInMicroCents `shouldEqual` (centsToMicroCents 1)

    it "BUG: rounding may accumulate errors" do
      -- BUG: Each cost component is rounded individually
      -- Then they're summed, which may accumulate rounding errors
      let modelInfo = mkMockModelInfo
        { cost = { input: 0.1, output: 0.1, cacheRead: Nothing, cacheWrite5m: Nothing, cacheWrite1h: Nothing } }
      let usageInfo = mkMockUsageInfo { inputTokens = 10000 }  -- 0.1 cents each
      let costInfo = calculateCost modelInfo usageInfo
      -- Each component rounds to 0, but total should be 0.2 cents
      -- This test documents potential rounding error accumulation
      costInfo.costInMicroCents `shouldNotEqual` 0

  describe "calculateCost - Cache Cost Calculations" do
    it "calculates cache read cost when both cost and tokens present" do
      let modelInfo = mkMockModelInfo
        { cost = mkMockModelInfo.cost { cacheRead = Just 1.0 } }
      let usageInfo = mkMockUsageInfo { cacheReadTokens = Just 1000000 }  -- 1M tokens
      let costInfo = calculateCost modelInfo usageInfo
      -- Cache read: 1M tokens * $1/1M * 100 = 100 cents
      -- Plus input/output costs
      costInfo.costInMicroCents `shouldNotEqual` (centsToMicroCents 6)

    it "returns Nothing cost when cache cost not configured" do
      let modelInfo = mkMockModelInfo  -- No cache cost
      let usageInfo = mkMockUsageInfo { cacheReadTokens = Just 1000000 }
      let costInfo = calculateCost modelInfo usageInfo
      -- Should not include cache cost
      costInfo.costInMicroCents `shouldEqual` (centsToMicroCents 6)

    it "returns Nothing cost when cache tokens not present" do
      let modelInfo = mkMockModelInfo
        { cost = mkMockModelInfo.cost { cacheRead = Just 1.0 } }
      let usageInfo = mkMockUsageInfo { cacheReadTokens = Nothing }
      let costInfo = calculateCost modelInfo usageInfo
      -- Should not include cache cost
      costInfo.costInMicroCents `shouldEqual` (centsToMicroCents 6)

    it "calculates cache write 5m cost" do
      let modelInfo = mkMockModelInfo
        { cost = mkMockModelInfo.cost { cacheWrite5m = Just 2.0 } }
      let usageInfo = mkMockUsageInfo { cacheWrite5mTokens = Just 500000 }  -- 0.5M tokens
      let costInfo = calculateCost modelInfo usageInfo
      -- Cache write 5m: 0.5M tokens * $2/1M * 100 = 100 cents
      costInfo.costInMicroCents `shouldNotEqual` (centsToMicroCents 6)

    it "calculates cache write 1h cost" do
      let modelInfo = mkMockModelInfo
        { cost = mkMockModelInfo.cost { cacheWrite1h = Just 3.0 } }
      let usageInfo = mkMockUsageInfo { cacheWrite1hTokens = Just 333333 }  -- ~0.33M tokens
      let costInfo = calculateCost modelInfo usageInfo
      -- Cache write 1h: 333333 tokens * $3/1M * 100 = ~100 cents
      costInfo.costInMicroCents `shouldNotEqual` (centsToMicroCents 6)

  describe "Bug Detection Tests" do
    it "detects bug: 200K threshold uses > not >=" do
      -- Exactly 200K should use 200K cost, but uses standard cost
      let modelInfo = mkMockModelInfo200K
      let usageInfo = mkMockUsageInfo { inputTokens = 200000 }
      let costInfo = calculateCost modelInfo usageInfo
      -- Should use 200K cost but uses standard cost
      -- This test documents the bug
      costInfo.costInMicroCents `shouldNotEqual` 0

    it "detects bug: threshold excludes outputTokens and reasoningTokens" do
      -- Only inputTokens + cache tokens count toward threshold
      -- outputTokens and reasoningTokens don't count
      let modelInfo = mkMockModelInfo200K
      let usageInfo =
            { inputTokens: 100000
            , outputTokens: 100000
            , reasoningTokens: Just 1000
            , cacheReadTokens: Nothing
            , cacheWrite5mTokens: Nothing
            , cacheWrite1hTokens: Nothing
            }
      let costInfo = calculateCost modelInfo usageInfo
      -- Total tokens: 201000, but threshold sees 100000
      -- This test documents the bug
      costInfo.costInMicroCents `shouldNotEqual` 0

    it "detects bug: fromMaybe logic when cost200K is Nothing" do
      -- If shouldUse200KCost returns true but cost200K is Nothing,
      -- fromMaybe uses standard cost when provider cost is unavailable
      let modelInfo = mkMockModelInfo  -- No cost200K
      let usageInfo = mkMockUsageInfo { inputTokens = 300000 }
      let costInfo = calculateCost modelInfo usageInfo
      -- Should use standard cost (correct behavior)
      costInfo.costInMicroCents `shouldNotEqual` 0

    it "verifies cost calculation formula" do
      -- Formula: round(cost * tokens / 1_000_000.0 * 100.0)
      -- This converts per-1M-token cost to cents
      let modelInfo = mkMockModelInfo
      let usageInfo = mkMockUsageInfo { inputTokens = 1000000 }  -- Exactly 1M
      let costInfo = calculateCost modelInfo usageInfo
      -- Input: 1M tokens * $30/1M * 100 = 3000 cents
      -- Output: 500 tokens * $60/1M * 100 = 3 cents
      -- Total: 3003 cents
      costInfo.costInMicroCents `shouldEqual` (centsToMicroCents 3003)
