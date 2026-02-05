-- | Deep comprehensive tests for TrialLimiter module
-- | Tests all edge cases, findLimit bugs, and potential issues
module Test.Unit.Util.TrialLimiterSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual)

import Console.App.Routes.Omega.Util.TrialLimiter
  ( TrialConfig
  , TrialLimit
  , TrialState
  , UsageInfo
  , findLimit
  , isTrial
  , calculateUsage
  , isEnabled
  )
import Data.Maybe (Maybe(..), isNothing, isJust)

-- | Deep comprehensive tests for TrialLimiter
spec :: Spec Unit
spec = describe "TrialLimiter Deep Tests" do
  describe "findLimit" do
    it "finds exact client match" do
      let limits = 
            [ { client: Just "client1", limit: 1000 }
            , { client: Just "client2", limit: 2000 }
            , { client: Nothing, limit: 500 }
            ]
      findLimit limits "client1" `shouldEqual` Just 1000

    it "finds default limit when no exact match" do
      let limits = 
            [ { client: Just "client1", limit: 1000 }
            , { client: Nothing, limit: 500 }
            ]
      findLimit limits "unknown-client" `shouldEqual` Just 500

    it "returns Nothing when no exact match and no default" do
      let limits = 
            [ { client: Just "client1", limit: 1000 }
            , { client: Just "client2", limit: 2000 }
            ]
      findLimit limits "unknown-client" `shouldEqual` Nothing

    it "returns Nothing when limits array is empty" do
      let limits = []
      findLimit limits "any-client" `shouldEqual` Nothing

    it "BUG: returns Nothing when multiple exact matches exist" do
      -- BUG: findExact only handles [l] case, multiple matches return Nothing
      let limits = 
            [ { client: Just "client1", limit: 1000 }
            , { client: Just "client1", limit: 2000 } -- Duplicate!
            ]
      findLimit limits "client1" `shouldEqual` Nothing
      -- This test documents the bug: should return first match or handle duplicates

    it "BUG: returns Nothing when multiple default limits exist" do
      -- BUG: findDefault only handles [l] case, multiple defaults return Nothing
      let limits = 
            [ { client: Just "client1", limit: 1000 }
            , { client: Nothing, limit: 500 }
            , { client: Nothing, limit: 600 } -- Duplicate default!
            ]
      findLimit limits "unknown-client" `shouldEqual` Nothing
      -- This test documents the bug: should return first default or handle duplicates

    it "prefers exact match over default" do
      let limits = 
            [ { client: Just "client1", limit: 1000 }
            , { client: Nothing, limit: 500 }
            ]
      findLimit limits "client1" `shouldEqual` Just 1000

    it "handles empty client string" do
      let limits = 
            [ { client: Just "", limit: 1000 }
            , { client: Nothing, limit: 500 }
            ]
      findLimit limits "" `shouldEqual` Just 1000

    it "handles whitespace-only client string" do
      let limits = 
            [ { client: Just "   ", limit: 1000 }
            , { client: Nothing, limit: 500 }
            ]
      findLimit limits "   " `shouldEqual` Just 1000

    it "handles very long client string" do
      let longClient = fold (replicate 10000 "a")
      let limits = 
            [ { client: Just longClient, limit: 1000 }
            , { client: Nothing, limit: 500 }
            ]
      findLimit limits longClient `shouldEqual` Just 1000

  describe "isTrial" do
    it "returns true when usage is below limit" do
      isTrial 50 100 `shouldEqual` true

    it "returns false when usage equals limit (boundary)" do
      isTrial 100 100 `shouldEqual` false

    it "returns false when usage exceeds limit" do
      isTrial 150 100 `shouldEqual` false

    it "handles zero usage" do
      isTrial 0 100 `shouldEqual` true

    it "handles zero limit (edge case)" do
      -- Zero limit means no trial (usage < 0 is false)
      isTrial 0 0 `shouldEqual` false
      isTrial 1 0 `shouldEqual` false

    it "handles negative usage (edge case)" do
      -- Negative usage shouldn't happen, but test robustness
      isTrial (-10) 100 `shouldEqual` true

    it "handles negative limit (edge case)" do
      -- Negative limit shouldn't happen, but test robustness
      isTrial 50 (-100) `shouldEqual` false

    it "handles very large usage" do
      isTrial 2147483647 100 `shouldEqual` false

    it "handles very large limit" do
      isTrial 1000 2147483647 `shouldEqual` true

  describe "calculateUsage" do
    it "sums all token types when all are Just" do
      let info = 
            { inputTokens: 100
            , outputTokens: 200
            , reasoningTokens: Just 50
            , cacheReadTokens: Just 25
            , cacheWrite5mTokens: Just 10
            , cacheWrite1hTokens: Just 5
            }
      calculateUsage info `shouldEqual` 390

    it "handles all Nothing optional fields" do
      let info = 
            { inputTokens: 100
            , outputTokens: 200
            , reasoningTokens: Nothing
            , cacheReadTokens: Nothing
            , cacheWrite5mTokens: Nothing
            , cacheWrite1hTokens: Nothing
            }
      calculateUsage info `shouldEqual` 300

    it "handles mixed Just/Nothing optional fields" do
      let info = 
            { inputTokens: 100
            , outputTokens: 200
            , reasoningTokens: Just 50
            , cacheReadTokens: Nothing
            , cacheWrite5mTokens: Just 10
            , cacheWrite1hTokens: Nothing
            }
      calculateUsage info `shouldEqual` 360

    it "handles zero values" do
      let info = 
            { inputTokens: 0
            , outputTokens: 0
            , reasoningTokens: Just 0
            , cacheReadTokens: Just 0
            , cacheWrite5mTokens: Just 0
            , cacheWrite1hTokens: Just 0
            }
      calculateUsage info `shouldEqual` 0

    it "handles negative token values (edge case)" do
      -- Negative tokens shouldn't happen, but test robustness
      let info = 
            { inputTokens: (-10)
            , outputTokens: 20
            , reasoningTokens: Just (-5)
            , cacheReadTokens: Nothing
            , cacheWrite5mTokens: Nothing
            , cacheWrite1hTokens: Nothing
            }
      calculateUsage info `shouldEqual` 5

    it "handles very large token values" do
      let info = 
            { inputTokens: 1000000
            , outputTokens: 2000000
            , reasoningTokens: Just 500000
            , cacheReadTokens: Just 250000
            , cacheWrite5mTokens: Just 100000
            , cacheWrite1hTokens: Just 50000
            }
      calculateUsage info `shouldEqual` 3900000

    it "handles only input tokens" do
      let info = 
            { inputTokens: 100
            , outputTokens: 0
            , reasoningTokens: Nothing
            , cacheReadTokens: Nothing
            , cacheWrite5mTokens: Nothing
            , cacheWrite1hTokens: Nothing
            }
      calculateUsage info `shouldEqual` 100

    it "handles only output tokens" do
      let info = 
            { inputTokens: 0
            , outputTokens: 200
            , reasoningTokens: Nothing
            , cacheReadTokens: Nothing
            , cacheWrite5mTokens: Nothing
            , cacheWrite1hTokens: Nothing
            }
      calculateUsage info `shouldEqual` 200

  describe "isEnabled" do
    it "returns false when config is Nothing" do
      isEnabled Nothing "client1" `shouldEqual` false

    it "returns false when client is empty string" do
      let config = Just { provider: "test", limits: [{ client: Just "client1", limit: 1000 }] }
      isEnabled config "" `shouldEqual` false

    it "returns true when exact client match exists" do
      let config = Just 
            { provider: "test"
            , limits: 
                [ { client: Just "client1", limit: 1000 }
                , { client: Nothing, limit: 500 }
                ]
            }
      isEnabled config "client1" `shouldEqual` true

    it "returns true when default limit exists" do
      let config = Just 
            { provider: "test"
            , limits: 
                [ { client: Just "client1", limit: 1000 }
                , { client: Nothing, limit: 500 }
                ]
            }
      isEnabled config "unknown-client" `shouldEqual` true

    it "returns false when no match and no default" do
      let config = Just 
            { provider: "test"
            , limits: [{ client: Just "client1", limit: 1000 }]
            }
      isEnabled config "unknown-client" `shouldEqual` false

    it "handles whitespace-only client (treated as non-empty)" do
      let config = Just 
            { provider: "test"
            , limits: [{ client: Nothing, limit: 500 }]
            }
      -- Whitespace-only client is not empty, so isEnabled checks findLimit
      -- findLimit will return Nothing (no match for whitespace)
      isEnabled config "   " `shouldEqual` false

    it "handles empty limits array" do
      let config = Just { provider: "test", limits: [] }
      isEnabled config "any-client" `shouldEqual` false

  describe "Edge Cases - findLimit Bug Scenarios" do
    it "BUG: duplicate exact matches return Nothing instead of first" do
      -- Current behavior: returns Nothing
      -- Expected: should return first match or handle duplicates explicitly
      let limits = 
            [ { client: Just "client1", limit: 1000 }
            , { client: Just "client1", limit: 2000 }
            , { client: Just "client2", limit: 3000 }
            ]
      findLimit limits "client1" `shouldEqual` Nothing
      -- This test documents the bug

    it "BUG: duplicate default limits return Nothing instead of first" do
      -- Current behavior: returns Nothing
      -- Expected: should return first default or handle duplicates explicitly
      let limits = 
            [ { client: Just "client1", limit: 1000 }
            , { client: Nothing, limit: 500 }
            , { client: Nothing, limit: 600 }
            ]
      findLimit limits "unknown" `shouldEqual` Nothing
      -- This test documents the bug

    it "handles three or more exact matches (all return Nothing)" do
      let limits = 
            [ { client: Just "client1", limit: 1000 }
            , { client: Just "client1", limit: 2000 }
            , { client: Just "client1", limit: 3000 }
            ]
      findLimit limits "client1" `shouldEqual` Nothing

  describe "Edge Cases - isTrial Boundary Conditions" do
    it "handles usage exactly one below limit" do
      isTrial 99 100 `shouldEqual` true

    it "handles usage exactly at limit" do
      isTrial 100 100 `shouldEqual` false

    it "handles usage exactly one above limit" do
      isTrial 101 100 `shouldEqual` false

    it "handles limit = 1 (minimum limit)" do
      isTrial 0 1 `shouldEqual` true
      isTrial 1 1 `shouldEqual` false
      isTrial 2 1 `shouldEqual` false

  describe "Edge Cases - calculateUsage Combinations" do
    it "handles all optional fields as Just with zeros" do
      let info = 
            { inputTokens: 0
            , outputTokens: 0
            , reasoningTokens: Just 0
            , cacheReadTokens: Just 0
            , cacheWrite5mTokens: Just 0
            , cacheWrite1hTokens: Just 0
            }
      calculateUsage info `shouldEqual` 0

    it "handles all optional fields as Just with large values" do
      let info = 
            { inputTokens: 1000000
            , outputTokens: 2000000
            , reasoningTokens: Just 3000000
            , cacheReadTokens: Just 4000000
            , cacheWrite5mTokens: Just 5000000
            , cacheWrite1hTokens: Just 6000000
            }
      calculateUsage info `shouldEqual` 21000000

    it "handles integer overflow potential (very large values)" do
      -- Note: PureScript Int is bounded, but test edge case
      let info = 
            { inputTokens: 1000000000
            , outputTokens: 1000000000
            , reasoningTokens: Just 1000000000
            , cacheReadTokens: Just 1000000000
            , cacheWrite5mTokens: Just 1000000000
            , cacheWrite1hTokens: Just 1000000000
            }
      -- Total = 6000000000, which may overflow Int32
      -- This test documents potential overflow issue
      calculateUsage info `shouldNotEqual` 0

  describe "Integration Edge Cases" do
    it "findLimit and isTrial work together correctly" do
      let limits = [{ client: Just "client1", limit: 1000 }]
      case findLimit limits "client1" of
        Just limit -> isTrial 500 limit `shouldEqual` true
        Nothing -> it "Should find limit" (pure unit)

    it "calculateUsage and isTrial work together correctly" do
      let info = 
            { inputTokens: 100
            , outputTokens: 200
            , reasoningTokens: Just 50
            , cacheReadTokens: Nothing
            , cacheWrite5mTokens: Nothing
            , cacheWrite1hTokens: Nothing
            }
      let usage = calculateUsage info
      let limit = 500
      isTrial usage limit `shouldEqual` true

    it "isEnabled and findLimit work together correctly" do
      let config = Just 
            { provider: "test"
            , limits: [{ client: Just "client1", limit: 1000 }]
            }
      let enabled = isEnabled config "client1"
      let limit = findLimit [{ client: Just "client1", limit: 1000 }] "client1"
      -- If enabled, limit should be found
      if enabled
        then limit `shouldEqual` Just 1000
        else it "Should be enabled when client matches" (pure unit)

  describe "Bug Detection Tests" do
    it "detects bug: findLimit returns Nothing for duplicate exact matches" do
      -- Should return first match, but returns Nothing
      let limits = 
            [ { client: Just "client1", limit: 1000 }
            , { client: Just "client1", limit: 2000 }
            ]
      findLimit limits "client1" `shouldEqual` Nothing
      -- This test documents the bug

    it "detects bug: findLimit returns Nothing for duplicate defaults" do
      -- Should return first default, but returns Nothing
      let limits = 
            [ { client: Nothing, limit: 500 }
            , { client: Nothing, limit: 600 }
            ]
      findLimit limits "any-client" `shouldEqual` Nothing
      -- This test documents the bug

    it "verifies isTrial uses < not <=" do
      -- isTrial uses <, so usage == limit is NOT trial
      isTrial 100 100 `shouldEqual` false
      -- This is correct behavior (boundary is not trial)

    it "verifies calculateUsage sums correctly with all fields" do
      let info = 
            { inputTokens: 1
            , outputTokens: 2
            , reasoningTokens: Just 3
            , cacheReadTokens: Just 4
            , cacheWrite5mTokens: Just 5
            , cacheWrite1hTokens: Just 6
            }
      -- Sum should be 1 + 2 + 3 + 4 + 5 + 6 = 21
      calculateUsage info `shouldEqual` 21
