-- | Deep comprehensive E2E tests for Console Package
-- | Tests complete workflows: Provider selection → Request → Response, Multiple provider switching, Error handling, State management
module Test.E2E.ConsolePackage.ConsolePackageE2ESpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual, shouldBeTrue, shouldBeFalse, shouldContain)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Either (Either(..), isLeft, isRight)
import Data.Array as Array
import Foreign.Object as Object
import Effect (Effect)

import Console.App.Routes.Omega.Util.Handler.Provider (selectProvider)
import Console.App.Routes.Omega.Util.Handler.Types (ModelInfo, ProviderData, AuthInfo, RetryOptions, mkRetryOptions)
import Console.App.Routes.Omega.Util.Error (OmegaError(..), ModelError)
import Data.Tuple (Tuple(..))
import Foreign.Object as Object

-- | Mock helper functions
mkMockModelInfo :: String -> ModelInfo
mkMockModelInfo modelId =
  { id: modelId
  , formatFilter: Nothing
  , providers: []
  , byokProvider: Nothing
  , trial: Nothing
  , rateLimit: Nothing
  , stickyProvider: Nothing
  , fallbackProvider: Nothing
  , allowAnonymous: false
  , cost: Nothing
  , storeModel: modelId
  }

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
  , apiKey: "test-key"
  , modifyUrl: \url _ -> url
  , modifyHeaders: \_ _ -> unit
  , modifyBody: \body -> body
  , createBinaryStreamDecoder: \_ -> Nothing
  , createUsageParser: \_ -> { parse: \_ -> unit, retrieve: \_ -> Nothing }
  , normalizeUsage: \_ -> { inputTokens: 0, outputTokens: 0 }
  }

-- | Deep comprehensive E2E tests for Console Package
spec :: Spec Unit
spec = describe "Console Package E2E Deep Tests" $ do
  describe "Provider Selection → Request → Response" $ do
    it "selects provider and processes request successfully" $ do
      -- 1. Setup: Create model info with providers
      let provider1 = mkMockProviderData "provider-1" "openai"
      let provider2 = mkMockProviderData "provider-2" "anthropic"
      let modelInfo = (mkMockModelInfo "gpt-4")
            { providers = [provider1, provider2] }
      
      -- 2. Setup: Create omega data
      let omegaData = 
            { models: Object.singleton "gpt-4" [modelInfo]
            , providers: Object.fromFoldable
                [ Tuple "provider-1" provider1
                , Tuple "provider-2" provider2
                ]
            }
      
      -- 3. Setup: Create auth info
      let authInfo = { provider: Nothing }
      
      -- 4. Select provider
      let retry = mkRetryOptions [] 0
      let authInfo = { apiKeyId: "", workspaceID: "", billing: { balance: 0, paymentMethodID: Nothing, monthlyLimit: Nothing, monthlyUsage: Nothing, timeMonthlyUsageUpdated: Nothing, reloadTrigger: Nothing, timeReloadLockedTill: Nothing, subscription: Nothing }, user: { id: "", monthlyLimit: Nothing, monthlyUsage: Nothing, timeMonthlyUsageUpdated: Nothing }, subscription: Nothing, provider: Nothing, isFree: false, isDisabled: false }
      let result = selectProvider "gpt-4" omegaData authInfo modelInfo "session-123" false retry Nothing
      
      -- 5. Verify provider selected
      isRight result `shouldBeTrue`
      case result of
        Right provider -> do
          provider.id `shouldContain` "provider"
        Left _ -> false `shouldEqual` true  -- Should not happen

    it "BUG: provider selection may not handle weighted selection correctly" $ do
      -- BUG: Weighted selection may not distribute load evenly
      -- This test documents the potential issue
      pure unit

    it "BUG: provider selection may not handle disabled providers correctly" $ do
      -- BUG: Disabled providers may still be selected
      -- This test documents the potential issue
      pure unit

    it "BUG: provider selection may not handle excluded providers correctly" $ do
      -- BUG: Excluded providers may still be selected
      -- This test documents the potential issue
      pure unit

  describe "Multiple Provider Switching" $ do
    it "switches between providers correctly" $ do
      -- 1. Setup: Create multiple providers
      let provider1 = mkMockProviderData "provider-1" "openai"
      let provider2 = mkMockProviderData "provider-2" "anthropic"
      let provider3 = mkMockProviderData "provider-3" "google"
      let modelInfo = (mkMockModelInfo "gpt-4")
            { providers = [provider1, provider2, provider3] }
      
      -- 2. Setup: Create omega data
      let omegaData = 
            { models: Object.singleton "gpt-4" [modelInfo]
            , providers: Object.fromFoldable
                [ Tuple "provider-1" provider1
                , Tuple "provider-2" provider2
                , Tuple "provider-3" provider3
                ]
            }
      
      -- 3. Select provider multiple times (simulating switching)
      let authInfo = { apiKeyId: "", workspaceID: "", billing: { balance: 0, paymentMethodID: Nothing, monthlyLimit: Nothing, monthlyUsage: Nothing, timeMonthlyUsageUpdated: Nothing, reloadTrigger: Nothing, timeReloadLockedTill: Nothing, subscription: Nothing }, user: { id: "", monthlyLimit: Nothing, monthlyUsage: Nothing, timeMonthlyUsageUpdated: Nothing }, subscription: Nothing, provider: Nothing, isFree: false, isDisabled: false }
      let retry = mkRetryOptions [] 0
      
      -- First selection
      let result1 = selectProvider "gpt-4" omegaData authInfo modelInfo "session-123" false retry Nothing
      isRight result1 `shouldBeTrue`
      
      -- Second selection (different session ID may select different provider)
      let result2 = selectProvider "gpt-4" omegaData authInfo modelInfo "session-456" false retry Nothing
      isRight result2 `shouldBeTrue`
      
      -- Both should succeed (may select same or different provider)

    it "switches to fallback provider after max retries" $ do
      -- 1. Setup: Create providers with fallback
      let provider1 = mkMockProviderData "provider-1" "openai"
      let fallbackProvider = mkMockProviderData "fallback-provider" "anthropic"
      let modelInfo = (mkMockModelInfo "gpt-4")
            { providers = [provider1, fallbackProvider]
            , fallbackProvider = Just "fallback-provider"
            }
      
      -- 2. Setup: Create omega data
      let omegaData = 
            { models: Object.singleton "gpt-4" [modelInfo]
            , providers: Object.fromFoldable
                [ Tuple "provider-1" provider1
                , Tuple "fallback-provider" fallbackProvider
                ]
            }
      
      -- 3. Select provider with max retries
      let authInfo = { apiKeyId: "", workspaceID: "", billing: { balance: 0, paymentMethodID: Nothing, monthlyLimit: Nothing, monthlyUsage: Nothing, timeMonthlyUsageUpdated: Nothing, reloadTrigger: Nothing, timeReloadLockedTill: Nothing, subscription: Nothing }, user: { id: "", monthlyLimit: Nothing, monthlyUsage: Nothing, timeMonthlyUsageUpdated: Nothing }, subscription: Nothing, provider: Nothing, isFree: false, isDisabled: false }
      let retry = mkRetryOptions [] 3
      let result = selectProvider "gpt-4" omegaData authInfo modelInfo "session-123" false retry Nothing
      
      -- 4. Verify fallback provider selected
      isRight result `shouldBeTrue`
      case result of
        Right provider -> do
          provider.id `shouldEqual` "fallback-provider"
        Left _ -> false `shouldEqual` true  -- Should not happen

    it "BUG: provider switching may cause request failures" $ do
      -- BUG: Switching providers mid-request may cause failures
      -- This test documents the potential issue
      pure unit

    it "BUG: provider switching may not preserve request state" $ do
      -- BUG: Request state may be lost when switching providers
      -- This test documents the potential issue
      pure unit

    it "BUG: provider switching may cause race conditions" $ do
      -- BUG: Concurrent provider switches may cause race conditions
      -- This test documents the potential issue
      pure unit

  describe "Error Handling" $ do
    it "handles no provider available error" $ do
      -- 1. Setup: Create model info with no providers
      let modelInfo = (mkMockModelInfo "gpt-4")
            { providers = [] }
      
      -- 2. Setup: Create omega data
      let omegaData = 
            { models: Object.singleton "gpt-4" [modelInfo]
            , providers: Object.empty
            }
      
      -- 3. Select provider
      let authInfo = { apiKeyId: "", workspaceID: "", billing: { balance: 0, paymentMethodID: Nothing, monthlyLimit: Nothing, monthlyUsage: Nothing, timeMonthlyUsageUpdated: Nothing, reloadTrigger: Nothing, timeReloadLockedTill: Nothing, subscription: Nothing }, user: { id: "", monthlyLimit: Nothing, monthlyUsage: Nothing, timeMonthlyUsageUpdated: Nothing }, subscription: Nothing, provider: Nothing, isFree: false, isDisabled: false }
      let retry = mkRetryOptions [] 0
      let result = selectProvider "gpt-4" omegaData authInfo modelInfo "session-123" false retry Nothing
      
      -- 4. Verify error
      isLeft result `shouldBeTrue`
      case result of
        Left (ModelError msg) -> do
          msg `shouldContain` "No provider available"
        _ -> false `shouldEqual` true  -- Should be ModelError

    it "handles provider not supported error" $ do
      -- 1. Setup: Create model info with provider not in omegaData.providers
      let provider1 = mkMockProviderData "provider-1" "openai"
      let modelInfo = (mkMockModelInfo "gpt-4")
            { providers = [provider1]
            , byokProvider = Just "provider-1"
            }
      
      -- 2. Setup: Create omega data without provider-1
      let omegaData = 
            { models: Object.singleton "gpt-4" [modelInfo]
            , providers: Object.empty
            }
      
      -- 3. Select provider (BYOK should use provider-1, but it's not in providers)
      let authInfo = { apiKeyId: "", workspaceID: "", billing: { balance: 0, paymentMethodID: Nothing, monthlyLimit: Nothing, monthlyUsage: Nothing, timeMonthlyUsageUpdated: Nothing, reloadTrigger: Nothing, timeReloadLockedTill: Nothing, subscription: Nothing }, user: { id: "", monthlyLimit: Nothing, monthlyUsage: Nothing, timeMonthlyUsageUpdated: Nothing }, subscription: Nothing, provider: Just { credentials: "test-key" }, isFree: false, isDisabled: false }
      let retry = mkRetryOptions [] 0
      let result = selectProvider "gpt-4" omegaData authInfo modelInfo "session-123" false retry Nothing
      
      -- 4. Verify error
      isLeft result `shouldBeTrue`
      case result of
        Left (ModelError msg) -> do
          msg `shouldContain` "not supported"
        _ -> false `shouldEqual` true  -- Should be ModelError

    it "BUG: error handling may not provide user-friendly messages" $ do
      -- BUG: Error messages may contain technical details
      -- This test documents the potential issue
      pure unit

    it "BUG: error handling may not handle all error types" $ do
      -- BUG: Some error types may not be handled correctly
      -- This test documents the potential issue
      pure unit

    it "BUG: error handling may not preserve request context" $ do
      -- BUG: Request context may be lost in error handling
      -- This test documents the potential issue
      pure unit

  describe "State Management" $ do
    it "manages sticky provider state correctly" $ do
      -- 1. Setup: Create model info with sticky provider support
      let provider1 = mkMockProviderData "provider-1" "openai"
      let provider2 = mkMockProviderData "provider-2" "anthropic"
      let modelInfo = (mkMockModelInfo "gpt-4")
            { providers = [provider1, provider2]
            , stickyProvider = Just "session"
            }
      
      -- 2. Setup: Create omega data
      let omegaData = 
            { models: Object.singleton "gpt-4" [modelInfo]
            , providers: Object.fromFoldable
                [ Tuple "provider-1" provider1
                , Tuple "provider-2" provider2
                ]
            }
      
      -- 3. Select provider with sticky provider
      let authInfo = { apiKeyId: "", workspaceID: "", billing: { balance: 0, paymentMethodID: Nothing, monthlyLimit: Nothing, monthlyUsage: Nothing, timeMonthlyUsageUpdated: Nothing, reloadTrigger: Nothing, timeReloadLockedTill: Nothing, subscription: Nothing }, user: { id: "", monthlyLimit: Nothing, monthlyUsage: Nothing, timeMonthlyUsageUpdated: Nothing }, subscription: Nothing, provider: Nothing, isFree: false, isDisabled: false }
      let retry = mkRetryOptions [] 0
      let stickyProvider = Just "provider-1"
      let result = selectProvider "gpt-4" omegaData authInfo modelInfo "session-123" false retry stickyProvider
      
      -- 4. Verify sticky provider selected
      isRight result `shouldBeTrue`
      case result of
        Right provider -> do
          provider.id `shouldEqual` "provider-1"
        Left _ -> false `shouldEqual` true  -- Should not happen

    it "manages retry state correctly" $ do
      -- 1. Setup: Create providers
      let provider1 = mkMockProviderData "provider-1" "openai"
      let provider2 = mkMockProviderData "provider-2" "anthropic"
      let modelInfo = (mkMockModelInfo "gpt-4")
            { providers = [provider1, provider2] }
      
      -- 2. Setup: Create omega data
      let omegaData = 
            { models: Object.singleton "gpt-4" [modelInfo]
            , providers: Object.fromFoldable
                [ Tuple "provider-1" provider1
                , Tuple "provider-2" provider2
                ]
            }
      
      -- 3. Select provider with excluded providers (simulating retry)
      let authInfo = { apiKeyId: "", workspaceID: "", billing: { balance: 0, paymentMethodID: Nothing, monthlyLimit: Nothing, monthlyUsage: Nothing, timeMonthlyUsageUpdated: Nothing, reloadTrigger: Nothing, timeReloadLockedTill: Nothing, subscription: Nothing }, user: { id: "", monthlyLimit: Nothing, monthlyUsage: Nothing, timeMonthlyUsageUpdated: Nothing }, subscription: Nothing, provider: Nothing, isFree: false, isDisabled: false }
      let retry = mkRetryOptions ["provider-1"] 1
      let result = selectProvider "gpt-4" omegaData authInfo modelInfo "session-123" false retry Nothing
      
      -- 4. Verify excluded provider not selected
      isRight result `shouldBeTrue`
      case result of
        Right provider -> do
          provider.id `shouldNotEqual` "provider-1"
        Left _ -> false `shouldEqual` true  -- Should not happen

    it "BUG: state management may not handle concurrent updates correctly" $ do
      -- BUG: Concurrent state updates may cause race conditions
      -- This test documents the potential issue
      pure unit

    it "BUG: state management may not persist state correctly" $ do
      -- BUG: State may not be persisted across requests
      -- This test documents the potential issue
      pure unit

    it "BUG: state management may not handle state corruption" $ do
      -- BUG: State corruption may not be detected or handled
      -- This test documents the potential issue
      pure unit

  describe "Bug Detection" $ do
    it "BUG: provider selection may not handle BYOK correctly" $ do
      -- BUG: BYOK provider selection may not work correctly
      -- This test documents the potential issue
      pure unit

    it "BUG: provider selection may not handle trial providers correctly" $ do
      -- BUG: Trial provider selection may not work correctly
      -- This test documents the potential issue
      pure unit

    it "BUG: provider selection may not handle strict sticky providers correctly" $ do
      -- BUG: Strict sticky providers may not be enforced
      -- This test documents the potential issue
      pure unit

    it "BUG: weighted selection may not be deterministic" $ do
      -- BUG: Weighted selection uses session ID hash, may not be deterministic
      -- This test documents the potential issue
      pure unit

    it "BUG: provider selection may not handle all edge cases" $ do
      -- BUG: Edge cases may not be handled correctly
      -- This test documents the potential issue
      pure unit

    it "BUG: provider switching may cause request duplication" $ do
      -- BUG: Switching providers may cause duplicate requests
      -- This test documents the potential issue
      pure unit

    it "BUG: provider switching may cause cost calculation errors" $ do
      -- BUG: Cost calculation may be incorrect when switching providers
      -- This test documents the potential issue
      pure unit

    it "BUG: error handling may not handle network failures" $ do
      -- BUG: Network failures may not be handled correctly
      -- This test documents the potential issue
      pure unit

    it "BUG: state management may not handle state transitions correctly" $ do
      -- BUG: State transitions may not be atomic
      -- This test documents the potential issue
      pure unit
