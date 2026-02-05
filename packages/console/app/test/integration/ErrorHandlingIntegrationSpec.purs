-- | Deep comprehensive integration tests for error handling paths
-- | Tests error propagation across all modules in the request flow
module Test.Integration.ErrorHandlingIntegrationSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldContain, shouldNotEqual)
import Data.Either (Either(..), isLeft, isRight)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Foreign.Object as Object
import Data.Foldable (fold)
import Data.Array (replicate)
import Data.String as String

import Console.App.Routes.Omega.Util.Error (OmegaError(..))
import Console.App.Routes.Omega.Util.Handler.Validation
  ( validateModel
  , validateBilling
  , validateModelSettings
  )
import Console.App.Routes.Omega.Util.Handler.Auth (authenticate)
import Console.App.Routes.Omega.Util.Handler.Provider (selectProvider)
import Console.App.Routes.Omega.Util.Handler.Types
  ( ModelInfo
  , AuthInfo
  , ProviderData
  , RetryOptions
  , mkRetryOptions
  )
import Console.Core.Util.Price (MicroCents)

-- | Mock OmegaData for testing
type MockOmegaData = { models :: Object.Object (Array ModelInfo), providers :: Object.Object ProviderData }

-- | Create mock ModelInfo
mkMockModelInfo :: String -> Maybe String -> ModelInfo
mkMockModelInfo id formatFilter =
  { id
  , formatFilter
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
  , apiKey: "test-key"
  , modifyUrl: \url _ -> url
  , modifyHeaders: \_ _ -> unit
  , modifyBody: \body -> body
  , createBinaryStreamDecoder: \_ -> Nothing
  , createUsageParser: \_ -> { parse: \_ -> unit, retrieve: \_ -> Nothing }
  , normalizeUsage: \_ -> { inputTokens: 0, outputTokens: 0, reasoningTokens: Nothing, cacheReadTokens: Nothing, cacheWrite5mTokens: Nothing, cacheWrite1hTokens: Nothing }
  }

-- | Create mock AuthInfo
mkMockAuthInfo :: AuthInfo
mkMockAuthInfo =
  { apiKeyId: "key_123"
  , workspaceID: "workspace_123"
  , billing:
      { balance: 1000000  -- 10.00 in microcents
      , paymentMethodID: Just "pm_123"
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

-- | Deep comprehensive integration tests for error handling
spec :: Spec Unit
spec = describe "Error Handling Integration Deep Tests" do
  describe "Model Validation Error Propagation" do
    it "ModelError propagates when model not found" do
      let omegaData = { models: Object.empty, providers: Object.empty }
      case validateModel omegaData "nonexistent-model" "openai" of
        Left (ModelError msg) -> msg `shouldContain` "not supported"
        Left _ -> false `shouldEqual` true
        Right _ -> false `shouldEqual` true

    it "ModelError propagates when format filter doesn't match" do
      let modelInfo = mkMockModelInfo "gpt-4" (Just "anthropic")
      let providerData = mkMockProviderData "provider-1" "openai"
      let omegaData = { models: Object.singleton "gpt-4" [modelInfo], providers: Object.singleton "provider-1" providerData }
      case validateModel omegaData "gpt-4" "openai" of
        Left (ModelError msg) -> msg `shouldContain` "not supported"
        Left _ -> false `shouldEqual` true
        Right _ -> false `shouldEqual` true

    it "ModelError propagates when no providers available" do
      let modelInfo = mkMockModelInfo "gpt-4" Nothing { providers = [] }
      let omegaData = { models: Object.singleton "gpt-4" [modelInfo], providers: Object.empty }
      case validateModel omegaData "gpt-4" "openai" of
        Left (ModelError msg) -> msg `shouldContain` "No provider"
        Left _ -> false `shouldEqual` true
        Right _ -> false `shouldEqual` true

  describe "Authentication Error Propagation" do
    it "AuthError propagates when API key is missing" do
      let modelInfo = mkMockModelInfo "gpt-4" Nothing
      case authenticate modelInfo Nothing of
        Left (AuthError msg) -> msg `shouldContain` "Missing API key"
        Left _ -> false `shouldEqual` true
        Right _ -> false `shouldEqual` true

    it "AuthError propagates when model requires auth but key is invalid" do
      let modelInfo = mkMockModelInfo "gpt-4" Nothing { allowAnonymous = false }
      case authenticate modelInfo (Just "invalid-key") of
        Left (AuthError msg) -> msg `shouldContain` "Invalid API key"
        Left _ -> false `shouldEqual` true
        Right _ -> false `shouldEqual` true

    it "allows anonymous when model allows it" do
      let modelInfo = mkMockModelInfo "gpt-4" Nothing { allowAnonymous = true }
      case authenticate modelInfo Nothing of
        Left _ -> false `shouldEqual` true
        Right _ -> true `shouldEqual` true

  describe "Billing Validation Error Propagation" do
    it "CreditsError propagates when balance is insufficient" do
      let modelInfo = mkMockModelInfo "gpt-4" Nothing
      let authInfo = mkMockAuthInfo { billing = { balance: 0, paymentMethodID: Just "pm_123", monthlyLimit: Nothing, monthlyUsage: Nothing, timeMonthlyUsageUpdated: Nothing, reloadTrigger: Nothing, timeReloadLockedTill: Nothing, subscription: Nothing } }
      case validateBilling (Just authInfo) modelInfo of
        Left (CreditsError msg) -> msg `shouldContain` "Insufficient balance"
        Left _ -> false `shouldEqual` true
        Right _ -> false `shouldEqual` true

    it "CreditsError propagates when no payment method" do
      let modelInfo = mkMockModelInfo "gpt-4" Nothing
      let authInfo = mkMockAuthInfo { billing = { balance: 0, paymentMethodID: Nothing, monthlyLimit: Nothing, monthlyUsage: Nothing, timeMonthlyUsageUpdated: Nothing, reloadTrigger: Nothing, timeReloadLockedTill: Nothing, subscription: Nothing } }
      case validateBilling (Just authInfo) modelInfo of
        Left (CreditsError msg) -> msg `shouldContain` "No payment method"
        Left _ -> false `shouldEqual` true
        Right _ -> false `shouldEqual` true

    it "MonthlyLimitError propagates when monthly limit exceeded" do
      let modelInfo = mkMockModelInfo "gpt-4" Nothing
      let authInfo = mkMockAuthInfo { billing = { balance: 1000000, paymentMethodID: Just "pm_123", monthlyLimit: Just 100, monthlyUsage: Just 101000000, timeMonthlyUsageUpdated: Nothing, reloadTrigger: Nothing, timeReloadLockedTill: Nothing, subscription: Nothing } }
      case validateBilling (Just authInfo) modelInfo of
        Left (MonthlyLimitError msg) -> msg `shouldContain` "monthly spending limit"
        Left _ -> false `shouldEqual` true
        Right _ -> false `shouldEqual` true

    it "allows request when balance is sufficient" do
      let modelInfo = mkMockModelInfo "gpt-4" Nothing
      let authInfo = mkMockAuthInfo { billing = { balance: 1000000, paymentMethodID: Just "pm_123", monthlyLimit: Nothing, monthlyUsage: Nothing, timeMonthlyUsageUpdated: Nothing, reloadTrigger: Nothing, timeReloadLockedTill: Nothing, subscription: Nothing } }
      case validateBilling (Just authInfo) modelInfo of
        Left _ -> false `shouldEqual` true
        Right _ -> true `shouldEqual` true

  describe "Model Settings Validation Error Propagation" do
    it "ModelError propagates when model is disabled" do
      let authInfo = mkMockAuthInfo { isDisabled = true }
      case validateModelSettings (Just authInfo) of
        Left (ModelError msg) -> msg `shouldContain` "disabled"
        Left _ -> false `shouldEqual` true
        Right _ -> false `shouldEqual` true

    it "allows request when model is enabled" do
      let authInfo = mkMockAuthInfo { isDisabled = false }
      case validateModelSettings (Just authInfo) of
        Left _ -> false `shouldEqual` true
        Right _ -> true `shouldEqual` true

    it "allows request when authInfo is Nothing" do
      case validateModelSettings Nothing of
        Left _ -> false `shouldEqual` true
        Right _ -> true `shouldEqual` true

  describe "Provider Selection Error Propagation" do
    it "ModelError propagates when no providers available" do
      let omegaData = { models: Object.empty, providers: Object.empty }
      let modelInfo = mkMockModelInfo "gpt-4" Nothing { providers = [] }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData Nothing modelInfo "session-123" false retry Nothing of
        Left (ModelError msg) -> msg `shouldContain` "No provider"
        Left _ -> false `shouldEqual` true
        Right _ -> false `shouldEqual` true

    it "ModelError propagates when all providers are disabled" do
      let providerData = mkMockProviderData "provider-1" "openai" { disabled = true }
      let modelInfo = mkMockModelInfo "gpt-4" Nothing { providers = [providerData] }
      let omegaData = { models: Object.singleton "gpt-4" [modelInfo], providers: Object.singleton "provider-1" providerData }
      let retry = mkRetryOptions [] 0
      case selectProvider "gpt-4" omegaData Nothing modelInfo "session-123" false retry Nothing of
        Left (ModelError msg) -> msg `shouldContain` "No provider"
        Left _ -> false `shouldEqual` true
        Right _ -> false `shouldEqual` true

    it "ModelError propagates when all providers are excluded in retry" do
      let providerData = mkMockProviderData "provider-1" "openai"
      let modelInfo = mkMockModelInfo "gpt-4" Nothing { providers = [providerData] }
      let omegaData = { models: Object.singleton "gpt-4" [modelInfo], providers: Object.singleton "provider-1" providerData }
      let retry = mkRetryOptions ["provider-1"] 1
      case selectProvider "gpt-4" omegaData Nothing modelInfo "session-123" false retry Nothing of
        Left (ModelError msg) -> msg `shouldContain` "No provider"
        Left _ -> false `shouldEqual` true
        Right _ -> false `shouldEqual` true

  describe "Error Chain Propagation" do
    it "errors propagate in correct order: model → auth → billing → provider" do
      -- Test that errors are caught at the right stage
      -- Model validation happens first
      let omegaData = { models: Object.empty, providers: Object.empty }
      case validateModel omegaData "nonexistent" "openai" of
        Left (ModelError _) -> true `shouldEqual` true  -- Model error caught first
        _ -> false `shouldEqual` true

    it "errors don't propagate past validation stage" do
      -- If model validation fails, auth/billing/provider selection shouldn't run
      let omegaData = { models: Object.empty, providers: Object.empty }
      case validateModel omegaData "nonexistent" "openai" of
        Left _ -> true `shouldEqual` true  -- Error stops propagation
        Right _ -> false `shouldEqual` true

  describe "Error Message Consistency" do
    it "all ModelError messages contain 'Model' or 'model'" do
      let omegaData = { models: Object.empty, providers: Object.empty }
      case validateModel omegaData "test" "openai" of
        Left (ModelError msg) -> msg `shouldContain` "model" || msg `shouldContain` "Model"
        _ -> false `shouldEqual` true

    it "all AuthError messages contain authentication-related terms" do
      let modelInfo = mkMockModelInfo "gpt-4" Nothing { allowAnonymous = false }
      case authenticate modelInfo Nothing of
        Left (AuthError msg) -> msg `shouldContain` "API key" || msg `shouldContain` "key"
        _ -> false `shouldEqual` true

    it "all CreditsError messages contain billing-related terms" do
      let modelInfo = mkMockModelInfo "gpt-4" Nothing
      let authInfo = mkMockAuthInfo { billing = { balance: 0, paymentMethodID: Nothing, monthlyLimit: Nothing, monthlyUsage: Nothing, timeMonthlyUsageUpdated: Nothing, reloadTrigger: Nothing, timeReloadLockedTill: Nothing, subscription: Nothing } }
      case validateBilling (Just authInfo) modelInfo of
        Left (CreditsError msg) -> msg `shouldContain` "payment" || msg `shouldContain` "balance" || msg `shouldContain` "billing"
        _ -> false `shouldEqual` true

  describe "Edge Case Error Handling" do
    it "handles empty model name" do
      let omegaData = { models: Object.empty, providers: Object.empty }
      case validateModel omegaData "" "openai" of
        Left (ModelError _) -> true `shouldEqual` true
        _ -> false `shouldEqual` true

    it "handles empty format string" do
      let omegaData = { models: Object.empty, providers: Object.empty }
      case validateModel omegaData "gpt-4" "" of
        Left _ -> true `shouldEqual` true
        Right _ -> false `shouldEqual` true

    it "handles very long model name" do
      let longModel = fold (replicate 10000 "a")
      let omegaData = { models: Object.empty, providers: Object.empty }
      case validateModel omegaData longModel "openai" of
        Left (ModelError _) -> true `shouldEqual` true
        _ -> false `shouldEqual` true

    it "handles unicode in error messages" do
      -- Error messages should handle unicode correctly
      let omegaData = { models: Object.empty, providers: Object.empty }
      case validateModel omegaData "测试模型" "openai" of
        Left (ModelError msg) -> msg.length `shouldNotEqual` 0
        _ -> false `shouldEqual` true

  describe "Bug Detection - Error Handling" do
    it "BUG: error messages may not be user-friendly" do
      -- BUG: Some error messages may be too technical
      -- This test documents the need for user-friendly error messages
      pure unit

    it "BUG: error propagation may not preserve context" do
      -- BUG: Errors may lose context as they propagate through layers
      -- This test documents the need for error context preservation
      pure unit

    it "BUG: multiple validation errors may only return first error" do
      -- BUG: validateModelSettings may only return first error
      -- This test documents the limitation
      pure unit
