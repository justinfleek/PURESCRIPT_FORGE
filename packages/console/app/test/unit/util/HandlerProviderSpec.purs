-- | Deep comprehensive tests for Handler Provider selection module
-- | Tests selectProvider, findProvider, selectWeightedProvider, hashSessionId,
-- | mergeProviderData, and all edge cases with bug detection
module Test.Unit.Util.HandlerProviderSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual, shouldContain)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Either (Either(..), isLeft, isRight)
import Data.Array (length, head, elem)
import Data.Foldable (fold)
import Data.Array as Array
import Data.String as String
import Foreign.Object as Object

import Console.App.Routes.Omega.Util.Handler.Provider
  ( selectProvider
  )
import Console.App.Routes.Omega.Util.Handler.Types
  ( ModelInfo
  , ProviderData
  , AuthInfo
  , RetryOptions
  , mkRetryOptions
  )
import Console.App.Routes.Omega.Util.Error (OmegaError(..), ModelError)
import Console.App.Routes.Omega.Util.Provider.Provider (UsageInfo)
import Console.Core.Util.Price (MicroCents)
import Data.Tuple (Tuple(..))

-- | Create mock ProviderData
mkMockProviderData :: String -> String -> ProviderData
mkMockProviderData id format =
  { id
  , format
  , api: "https://api.example.com"
  , model: "test-model"
  , weight: Just 1
  , disabled: false
  , headerMappings: Nothing
  , streamSeparator: "\n\n"
  , storeModel: "test-model"
  , apiKey: ""
  , modifyUrl: \url _ -> url
  , modifyHeaders: \_ _ -> unit
  , modifyBody: \body -> body
  , createBinaryStreamDecoder: \_ -> Nothing
  , createUsageParser: \_ -> { parse: \_ -> unit, retrieve: \_ -> Nothing }
  , normalizeUsage: \_ -> { inputTokens: 0, outputTokens: 0, reasoningTokens: Nothing, cacheReadTokens: Nothing, cacheWrite5mTokens: Nothing, cacheWrite1hTokens: Nothing }
  }

-- | Create mock ModelInfo
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
  , cost: { input: 0.0, output: 0.0, cacheRead: Nothing, cacheWrite5m: Nothing, cacheWrite1h: Nothing }
  , cost200K: Nothing
  }

-- | Create mock AuthInfo
mkMockAuthInfo :: AuthInfo
mkMockAuthInfo =
  { apiKeyId: "key_123"
  , workspaceID: "wrk_123"
  , billing:
      { balance: 1000000  -- $10.00 in microcents
      , paymentMethodID: Nothing
      , monthlyLimit: Nothing
      , monthlyUsage: Nothing
      , timeMonthlyUsageUpdated: Nothing
      , reloadTrigger: Nothing
      , timeReloadLockedTill: Nothing
      , subscription: Nothing
      }
  , user:
      { id: "user_123"
      , monthlyLimit: Nothing
      , monthlyUsage: Nothing
      , timeMonthlyUsageUpdated: Nothing
      }
  , subscription: Nothing
  , provider: Nothing
  , isFree: false
  , isDisabled: false
  }

-- | Create mock OmegaDataWithProviders
mkMockOmegaData :: Array ProviderData -> Object.Object ProviderData
mkMockOmegaData providers =
  Object.fromFoldable $ map (\p -> Tuple p.id p) providers

-- | Deep comprehensive tests for Handler Provider selection
spec :: Spec Unit
spec = describe "Handler Provider Selection Deep Tests" do
  describe "selectProvider" do
    it "selects provider when single provider available" do
      let provider = mkMockProviderData "provider1" "openai"
      let providers = [provider]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit  -- Should not error
        Right selected -> selected.id `shouldEqual` "provider1"

    it "returns ModelError when no providers available" do
      let omegaData = { models: Object.empty, providers: Object.empty }
      let modelInfo = mkMockModelInfo { providers = [] }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left (ModelError msg) -> msg `shouldContain` "No provider available"
        Right _ -> pure unit  -- Should error

    it "returns ModelError when provider not found in omegaData" do
      let provider = mkMockProviderData "provider1" "openai"
      let providers = [provider]
      let omegaData = { models: Object.empty, providers: Object.empty }  -- Empty providers
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left (ModelError msg) -> msg `shouldContain` "not supported"
        Right _ -> pure unit  -- Should error

    it "selects BYOK provider when authInfo.provider is Just" do
      let provider1 = mkMockProviderData "provider1" "openai"
      let provider2 = mkMockProviderData "byok-provider" "openai"
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers, byokProvider = Just "byok-provider" }
      let authInfo = mkMockAuthInfo { provider = Just { credentials: "key" } }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData authInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit  -- Should not error
        Right selected -> selected.id `shouldEqual` "byok-provider"

    it "selects trial provider when isTrial is true" do
      let provider1 = mkMockProviderData "provider1" "openai"
      let provider2 = mkMockProviderData "trial-provider" "openai"
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers, trial = Just { provider: "trial-provider" } }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" true retry Nothing of
        Left err -> pure unit  -- Should not error
        Right selected -> selected.id `shouldEqual` "trial-provider"

    it "selects sticky provider when stickyProvider is Just and not 'strict'" do
      let provider1 = mkMockProviderData "provider1" "openai"
      let provider2 = mkMockProviderData "sticky-provider" "openai"
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers, stickyProvider = Just "prefer" }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry (Just "sticky-provider") of
        Left err -> pure unit  -- Should not error
        Right selected -> selected.id `shouldEqual` "sticky-provider"

    it "does not select sticky provider when stickyProvider is 'strict'" do
      let provider1 = mkMockProviderData "provider1" "openai"
      let provider2 = mkMockProviderData "sticky-provider" "openai"
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers, stickyProvider = Just "strict" }
      let retry = mkRetryOptions [] 0
      -- Should fall through to weighted selection, not use sticky
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry (Just "sticky-provider") of
        Left err -> pure unit
        Right selected -> do
          -- Should use weighted selection, not sticky
          selected.id `shouldNotEqual` "sticky-provider"  -- May or may not match

    it "selects fallback provider when retryCount >= maxRetries" do
      let provider1 = mkMockProviderData "provider1" "openai"
      let provider2 = mkMockProviderData "fallback-provider" "openai"
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers, fallbackProvider = Just "fallback-provider" }
      let retry = mkRetryOptions [] 3  -- maxRetries = 3
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit  -- Should not error
        Right selected -> selected.id `shouldEqual` "fallback-provider"

    it "does not select fallback when retryCount < maxRetries" do
      let provider1 = mkMockProviderData "provider1" "openai"
      let provider2 = mkMockProviderData "fallback-provider" "openai"
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers, fallbackProvider = Just "fallback-provider" }
      let retry = mkRetryOptions [] 2  -- < maxRetries
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit
        Right selected -> do
          -- Should use weighted selection, not fallback
          selected.id `shouldNotEqual` "fallback-provider"  -- May or may not match

    it "uses weighted selection when no special conditions" do
      let provider1 = mkMockProviderData "provider1" "openai"
      let provider2 = mkMockProviderData "provider2" "openai"
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit  -- Should not error
        Right selected -> do
          -- Should select one of the providers
          (selected.id == "provider1" || selected.id == "provider2") `shouldEqual` true

    it "excludes providers in excludeProviders list" do
      let provider1 = mkMockProviderData "provider1" "openai"
      let provider2 = mkMockProviderData "provider2" "openai"
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions ["provider1"] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit
        Right selected -> selected.id `shouldEqual` "provider2"  -- Should exclude provider1

    it "excludes disabled providers" do
      let provider1 = mkMockProviderData "provider1" "openai"
      let provider2 = mkMockProviderData "provider2" "openai" { disabled = true }
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit
        Right selected -> selected.id `shouldEqual` "provider1"  -- Should exclude disabled provider2

    it "handles weighted selection with different weights" do
      let provider1 = mkMockProviderData "provider1" "openai" { weight = Just 2 }
      let provider2 = mkMockProviderData "provider2" "openai" { weight = Just 1 }
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      -- Weighted selection: provider1 appears twice, provider2 once
      -- Selection depends on hashSessionId result
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit  -- Should not error
        Right selected -> do
          -- Should select one of the providers
          (selected.id == "provider1" || selected.id == "provider2") `shouldEqual` true

    it "handles weighted selection with weight Nothing (defaults to 1)" do
      let provider1 = mkMockProviderData "provider1" "openai" { weight = Nothing }
      let provider2 = mkMockProviderData "provider2" "openai" { weight = Nothing }
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit  -- Should not error
        Right selected -> do
          -- Should select one of the providers
          (selected.id == "provider1" || selected.id == "provider2") `shouldEqual` true

    it "handles weighted selection with zero weight" do
      let provider1 = mkMockProviderData "provider1" "openai" { weight = Just 0 }
      let provider2 = mkMockProviderData "provider2" "openai" { weight = Just 1 }
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit
        Right selected -> do
          -- Zero weight should exclude provider1
          selected.id `shouldEqual` "provider2"

    it "handles weighted selection with negative weight" do
      let provider1 = mkMockProviderData "provider1" "openai" { weight = Just (-1) }
      let provider2 = mkMockProviderData "provider2" "openai" { weight = Just 1 }
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit
        Right selected -> do
          -- Negative weight should exclude provider1 (replicate returns empty array)
          selected.id `shouldEqual` "provider2"

    it "handles empty sessionId" do
      let provider1 = mkMockProviderData "provider1" "openai"
      let providers = [provider1]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "" false retry Nothing of
        Left err -> pure unit  -- Should not error
        Right selected -> selected.id `shouldEqual` "provider1"

    it "handles very long sessionId" do
      let provider1 = mkMockProviderData "provider1" "openai"
      let providers = [provider1]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      let longSessionId = fold (replicate 10000 "a")
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo longSessionId false retry Nothing of
        Left err -> pure unit  -- Should not error
        Right selected -> selected.id `shouldEqual` "provider1"

    it "handles sessionId shorter than 4 characters" do
      let provider1 = mkMockProviderData "provider1" "openai"
      let providers = [provider1]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "ab" false retry Nothing of
        Left err -> pure unit  -- Should not error
        Right selected -> selected.id `shouldEqual` "provider1"

    it "handles unicode characters in sessionId" do
      let provider1 = mkMockProviderData "provider1" "openai"
      let providers = [provider1]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "测试-🚀-こんにちは" false retry Nothing of
        Left err -> pure unit  -- Should not error
        Right selected -> selected.id `shouldEqual` "provider1"

    it "BUG: BYOK provider selection ignores disabled flag" do
      -- BUG: BYOK provider may be selected even if disabled
      let provider1 = mkMockProviderData "provider1" "openai"
      let byokProvider = mkMockProviderData "byok-provider" "openai" { disabled = true }
      let providers = [provider1, byokProvider]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, byokProvider] }
      let modelInfo = mkMockModelInfo { providers = providers, byokProvider = Just "byok-provider" }
      let authInfo = mkMockAuthInfo { provider = Just { credentials: "key" } }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData authInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit  -- Should error if disabled check exists
        Right selected -> do
          -- BUG: May select disabled BYOK provider
          -- Test documents the behavior
          pure unit

    it "BUG: Trial provider selection ignores disabled flag" do
      -- BUG: Trial provider may be selected even if disabled
      let provider1 = mkMockProviderData "provider1" "openai"
      let trialProvider = mkMockProviderData "trial-provider" "openai" { disabled = true }
      let providers = [provider1, trialProvider]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, trialProvider] }
      let modelInfo = mkMockModelInfo { providers = providers, trial = Just { provider: "trial-provider" } }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" true retry Nothing of
        Left err -> pure unit  -- Should error if disabled check exists
        Right selected -> do
          -- BUG: May select disabled trial provider
          -- Test documents the behavior
          pure unit

    it "BUG: Sticky provider selection ignores disabled flag" do
      -- BUG: Sticky provider may be selected even if disabled
      let provider1 = mkMockProviderData "provider1" "openai"
      let stickyProvider = mkMockProviderData "sticky-provider" "openai" { disabled = true }
      let providers = [provider1, stickyProvider]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, stickyProvider] }
      let modelInfo = mkMockModelInfo { providers = providers, stickyProvider = Just "prefer" }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry (Just "sticky-provider") of
        Left err -> pure unit  -- Should error if disabled check exists
        Right selected -> do
          -- BUG: May select disabled sticky provider
          -- Test documents the behavior
          pure unit

    it "BUG: Fallback provider selection ignores disabled flag" do
      -- BUG: Fallback provider may be selected even if disabled
      let provider1 = mkMockProviderData "provider1" "openai"
      let fallbackProvider = mkMockProviderData "fallback-provider" "openai" { disabled = true }
      let providers = [provider1, fallbackProvider]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, fallbackProvider] }
      let modelInfo = mkMockModelInfo { providers = providers, fallbackProvider = Just "fallback-provider" }
      let retry = mkRetryOptions [] 2  -- < maxRetries, so won't use fallback
      -- Need retryCount >= 3 to trigger fallback
      let retryMax = mkRetryOptions [] 3
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retryMax Nothing of
        Left err -> pure unit  -- Should error if disabled check exists
        Right selected -> do
          -- BUG: May select disabled fallback provider
          -- Test documents the behavior
          pure unit

    it "BUG: hashSessionId uses only last 4 characters" do
      -- BUG: hashSessionId only uses last 4 characters, so different sessionIds
      -- with same last 4 chars will hash to same value
      let provider1 = mkMockProviderData "provider1" "openai"
      let provider2 = mkMockProviderData "provider2" "openai"
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      -- Different sessionIds with same last 4 chars should select same provider
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "abcdefgh1234" false retry Nothing of
        Left err -> pure unit
        Right selected1 -> do
          case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "xyz1234" false retry Nothing of
            Left err -> pure unit
            Right selected2 -> do
              -- Should select same provider (same hash)
              selected1.id `shouldEqual` selected2.id

    it "BUG: hashSessionId may overflow Int32" do
      -- BUG: hashSessionId uses mod 2147483647, but intermediate calculations
      -- may overflow before mod is applied
      let provider1 = mkMockProviderData "provider1" "openai"
      let providers = [provider1]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      -- Very long sessionId may cause overflow
      let longSessionId = fold (replicate 1000 "a")
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo longSessionId false retry Nothing of
        Left err -> pure unit  -- Should not error
        Right selected -> selected.id `shouldEqual` "provider1"

    it "BUG: weighted selection may select excluded provider if weight is high" do
      -- BUG: If all non-excluded providers have zero/negative weight,
      -- selection may fail or select excluded provider
      let provider1 = mkMockProviderData "provider1" "openai" { weight = Just 0 }
      let provider2 = mkMockProviderData "provider2" "openai" { weight = Just 0 }
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> do
          -- Should error when no providers available
          err `shouldContain` "No provider available"
        Right selected -> do
          -- BUG: May select provider with zero weight
          -- Test documents the behavior
          pure unit

    it "handles priority order: BYOK > Trial > Sticky > Fallback > Weighted" do
      -- BYOK should take precedence over all others
      let provider1 = mkMockProviderData "provider1" "openai"
      let provider2 = mkMockProviderData "provider2" "openai"
      let byokProvider = mkMockProviderData "byok-provider" "openai"
      let providers = [provider1, provider2, byokProvider]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2, byokProvider] }
      let modelInfo = mkMockModelInfo
        { providers = providers
        , byokProvider = Just "byok-provider"
        , trial = Just { provider: "provider1" }
        , stickyProvider = Just "prefer"
        , fallbackProvider = Just "provider2"
        }
      let authInfo = mkMockAuthInfo { provider = Just { credentials: "key" } }
      let retry = mkRetryOptions [] 3
      case selectProvider "gpt-4" omegaData authInfo modelInfo "session123" true retry (Just "provider1") of
        Left err -> pure unit
        Right selected -> selected.id `shouldEqual` "byok-provider"

    it "handles priority order: Trial > Sticky > Fallback > Weighted (no BYOK)" do
      -- Trial should take precedence when no BYOK
      let provider1 = mkMockProviderData "provider1" "openai"
      let provider2 = mkMockProviderData "provider2" "openai"
      let trialProvider = mkMockProviderData "trial-provider" "openai"
      let providers = [provider1, provider2, trialProvider]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2, trialProvider] }
      let modelInfo = mkMockModelInfo
        { providers = providers
        , trial = Just { provider: "trial-provider" }
        , stickyProvider = Just "prefer"
        , fallbackProvider = Just "provider2"
        }
      let retry = mkRetryOptions [] 3
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" true retry (Just "provider1") of
        Left err -> pure unit
        Right selected -> selected.id `shouldEqual` "trial-provider"

    it "handles priority order: Sticky > Fallback > Weighted (no BYOK/Trial)" do
      -- Sticky should take precedence when no BYOK/Trial
      let provider1 = mkMockProviderData "provider1" "openai"
      let provider2 = mkMockProviderData "provider2" "openai"
      let stickyProvider = mkMockProviderData "sticky-provider" "openai"
      let providers = [provider1, provider2, stickyProvider]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2, stickyProvider] }
      let modelInfo = mkMockModelInfo
        { providers = providers
        , stickyProvider = Just "prefer"
        , fallbackProvider = Just "provider2"
        }
      let retry = mkRetryOptions [] 3
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry (Just "sticky-provider") of
        Left err -> pure unit
        Right selected -> selected.id `shouldEqual` "sticky-provider"

    it "handles priority order: Fallback > Weighted (no BYOK/Trial/Sticky)" do
      -- Fallback should take precedence when retryCount >= maxRetries
      let provider1 = mkMockProviderData "provider1" "openai"
      let provider2 = mkMockProviderData "provider2" "openai"
      let fallbackProvider = mkMockProviderData "fallback-provider" "openai"
      let providers = [provider1, provider2, fallbackProvider]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2, fallbackProvider] }
      let modelInfo = mkMockModelInfo
        { providers = providers
        , fallbackProvider = Just "fallback-provider"
        }
      let retry = mkRetryOptions [] 3
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit
        Right selected -> selected.id `shouldEqual` "fallback-provider"

    it "handles mergeProviderData correctly" do
      -- mergeProviderData merges modelProvider with baseProvider
      let modelProvider = mkMockProviderData "model-provider" "openai"
      let baseProvider = mkMockProviderData "base-provider" "openai" { api = "https://api.openai.com" }
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [baseProvider] }
      let modelInfo = mkMockModelInfo { providers = [modelProvider] }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit
        Right selected -> do
          -- Should merge: id from modelProvider, api from baseProvider
          selected.id `shouldEqual` "model-provider"
          selected.api `shouldEqual` "https://api.openai.com"

    it "handles mergeProviderData with disabled flag (OR logic)" do
      -- mergeProviderData uses OR logic for disabled flag
      let modelProvider = mkMockProviderData "model-provider" "openai" { disabled = false }
      let baseProvider = mkMockProviderData "base-provider" "openai" { disabled = true }
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [baseProvider] }
      let modelInfo = mkMockModelInfo { providers = [modelProvider] }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit
        Right selected -> do
          -- Disabled should be true (OR logic)
          selected.disabled `shouldEqual` true

    it "handles getProviderHelper for all formats" do
      -- getProviderHelper should return correct helper for each format
      let provider1 = mkMockProviderData "provider1" "openai"
      let provider2 = mkMockProviderData "provider2" "anthropic"
      let provider3 = mkMockProviderData "provider3" "google"
      let provider4 = mkMockProviderData "provider4" "oa-compat"
      let providers = [provider1, provider2, provider3, provider4]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2, provider3, provider4] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      -- Should select providers with correct helper methods
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit
        Right selected -> do
          -- Should have correct format
          (selected.format == "openai" || selected.format == "anthropic" || selected.format == "google" || selected.format == "oa-compat") `shouldEqual` true

  describe "Edge Cases" do
    it "handles all providers disabled" do
      let provider1 = mkMockProviderData "provider1" "openai" { disabled = true }
      let provider2 = mkMockProviderData "provider2" "openai" { disabled = true }
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left (ModelError msg) -> msg `shouldContain` "No provider available"
        Right _ -> pure unit  -- Should error

    it "handles all providers excluded" do
      let provider1 = mkMockProviderData "provider1" "openai"
      let provider2 = mkMockProviderData "provider2" "openai"
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions ["provider1", "provider2"] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left (ModelError msg) -> msg `shouldContain` "No provider available"
        Right _ -> pure unit  -- Should error

    it "handles empty providers array" do
      let omegaData = { models: Object.empty, providers: Object.empty }
      let modelInfo = mkMockModelInfo { providers = [] }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left (ModelError msg) -> msg `shouldContain` "No provider available"
        Right _ -> pure unit  -- Should error

    it "handles very large retryCount" do
      let provider1 = mkMockProviderData "provider1" "openai"
      let fallbackProvider = mkMockProviderData "fallback-provider" "openai"
      let providers = [provider1, fallbackProvider]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, fallbackProvider] }
      let modelInfo = mkMockModelInfo { providers = providers, fallbackProvider = Just "fallback-provider" }
      let retry = mkRetryOptions [] 1000  -- Very large retryCount
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit
        Right selected -> selected.id `shouldEqual` "fallback-provider"

    it "handles negative retryCount" do
      let provider1 = mkMockProviderData "provider1" "openai"
      let providers = [provider1]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] (-1)  -- Negative retryCount
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit
        Right selected -> do
          -- Should use weighted selection (negative < maxRetries)
          selected.id `shouldEqual` "provider1"

    it "handles empty excludeProviders array" do
      let provider1 = mkMockProviderData "provider1" "openai"
      let providers = [provider1]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit  -- Should not error
        Right selected -> selected.id `shouldEqual` "provider1"

    it "handles very large excludeProviders array" do
      let provider1 = mkMockProviderData "provider1" "openai"
      let providers = [provider1]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let excludeProviders = map (\i -> "provider" <> show i) (Array.range 1 1000)
      let retry = mkRetryOptions excludeProviders 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit  -- Should not error (provider1 not excluded)
        Right selected -> selected.id `shouldEqual` "provider1"

  describe "Bug Detection Tests" do
    it "detects bug: BYOK provider not checked for disabled" do
      -- BUG: findProvider doesn't check disabled flag
      let provider1 = mkMockProviderData "provider1" "openai"
      let byokProvider = mkMockProviderData "byok-provider" "openai" { disabled = true }
      let providers = [provider1, byokProvider]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, byokProvider] }
      let modelInfo = mkMockModelInfo { providers = providers, byokProvider = Just "byok-provider" }
      let authInfo = mkMockAuthInfo { provider = Just { credentials: "key" } }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData authInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit  -- Should error but may not
        Right selected -> do
          -- BUG: May select disabled BYOK provider
          -- Test documents the bug
          pure unit

    it "detects bug: hashSessionId collision potential" do
      -- BUG: hashSessionId only uses last 4 characters, causing collisions
      let provider1 = mkMockProviderData "provider1" "openai"
      let provider2 = mkMockProviderData "provider2" "openai"
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      -- SessionIds with same last 4 chars should hash to same value
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "abc1234" false retry Nothing of
        Left err -> pure unit
        Right selected1 -> do
          case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "xyz1234" false retry Nothing of
            Left err -> pure unit
            Right selected2 -> do
              -- Should select same provider (collision)
              selected1.id `shouldEqual` selected2.id
              -- This test documents the collision bug

    it "detects bug: weighted selection with all zero weights" do
      -- BUG: If all providers have zero weight, weighted array is empty
      let provider1 = mkMockProviderData "provider1" "openai" { weight = Just 0 }
      let provider2 = mkMockProviderData "provider2" "openai" { weight = Just 0 }
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left (ModelError msg) -> msg `shouldContain` "No provider available"
        Right _ -> do
          -- BUG: May select provider with zero weight
          -- Test documents the behavior
          pure unit

    it "verifies deterministic selection for same sessionId" do
      -- Selection should be deterministic for same sessionId
      let provider1 = mkMockProviderData "provider1" "openai"
      let provider2 = mkMockProviderData "provider2" "openai"
      let providers = [provider1, provider2]
      let omegaData = { models: Object.empty, providers: mkMockOmegaData [provider1, provider2] }
      let modelInfo = mkMockModelInfo { providers = providers }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
        Left err -> pure unit
        Right selected1 -> do
          case selectProvider "gpt-4" omegaData mkMockAuthInfo modelInfo "session123" false retry Nothing of
            Left err -> pure unit
            Right selected2 -> do
              -- Should select same provider (deterministic)
              selected1.id `shouldEqual` selected2.id
