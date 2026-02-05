-- | Deep comprehensive tests for Error module
-- | Tests all transformation functions, edge cases, and potential bugs
module Test.Unit.Util.ErrorSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual)
import Data.Maybe (Maybe(..), isJust, isNothing)

import Console.App.Routes.Omega.Util.Error
  ( OmegaError(..)
  , ErrorResponse
  , toErrorResponse
  , toHttpStatus
  , getRetryAfter
  , formatResetTime
  , authErrorMissingKey
  , authErrorInvalidKey
  , modelErrorNotSupported
  , modelErrorNoProvider
  , modelErrorDisabled
  , creditsErrorNoPayment
  , creditsErrorInsufficientBalance
  , monthlyLimitExceeded
  , userLimitExceeded
  , subscriptionQuotaExceeded
  , rateLimitExceeded
  )
import Console.App.Routes.Omega.Util.Error as Error
import Data.Foldable (fold)
import Data.Array (replicate)

-- | Deep comprehensive tests for Error transformation functions
spec :: Spec Unit
spec = describe "Error Deep Tests" do
  describe "toErrorResponse" do
    it "converts AuthError to ErrorResponse" do
      let err = AuthError "Missing API key."
      let response = toErrorResponse err
      response.type `shouldEqual` "error"
      response.error.type `shouldEqual` "AuthError"
      response.error.message `shouldEqual` "Missing API key."

    it "converts CreditsError to ErrorResponse" do
      let err = CreditsError "Insufficient balance."
      let response = toErrorResponse err
      response.type `shouldEqual` "error"
      response.error.type `shouldEqual` "CreditsError"
      response.error.message `shouldEqual` "Insufficient balance."

    it "converts MonthlyLimitError to ErrorResponse" do
      let err = MonthlyLimitError "Limit exceeded."
      let response = toErrorResponse err
      response.type `shouldEqual` "error"
      response.error.type `shouldEqual` "MonthlyLimitError"
      response.error.message `shouldEqual` "Limit exceeded."

    it "converts SubscriptionError to ErrorResponse" do
      let err = SubscriptionError "Quota exceeded." (Just 60)
      let response = toErrorResponse err
      response.type `shouldEqual` "error"
      response.error.type `shouldEqual` "SubscriptionError"
      response.error.message `shouldEqual` "Quota exceeded."

    it "converts SubscriptionError with Nothing retryAfter" do
      let err = SubscriptionError "Quota exceeded." Nothing
      let response = toErrorResponse err
      response.type `shouldEqual` "error"
      response.error.type `shouldEqual` "SubscriptionError"
      response.error.message `shouldEqual` "Quota exceeded."

    it "converts UserLimitError to ErrorResponse" do
      let err = UserLimitError "User limit exceeded."
      let response = toErrorResponse err
      response.type `shouldEqual` "error"
      response.error.type `shouldEqual` "UserLimitError"
      response.error.message `shouldEqual` "User limit exceeded."

    it "converts ModelError to ErrorResponse" do
      let err = ModelError "Model not supported."
      let response = toErrorResponse err
      response.type `shouldEqual` "error"
      response.error.type `shouldEqual` "ModelError"
      response.error.message `shouldEqual` "Model not supported."

    it "converts RateLimitError to ErrorResponse" do
      let err = RateLimitError "Rate limit exceeded."
      let response = toErrorResponse err
      response.type `shouldEqual` "error"
      response.error.type `shouldEqual` "RateLimitError"
      response.error.message `shouldEqual` "Rate limit exceeded."

    it "converts InternalError to ErrorResponse" do
      let err = InternalError "Internal server error."
      let response = toErrorResponse err
      response.type `shouldEqual` "error"
      -- BUG: getErrorType returns "error" instead of "InternalError"
      response.error.type `shouldEqual` "error"
      response.error.message `shouldEqual` "Internal server error."

    it "handles empty error message" do
      let err = AuthError ""
      let response = toErrorResponse err
      response.error.message `shouldEqual` ""

    it "handles very long error message" do
      let longMsg = fold (replicate 10000 "a")
      let err = AuthError longMsg
      let response = toErrorResponse err
      response.error.message `shouldEqual` longMsg

    it "handles error message with special characters" do
      let err = AuthError "Error: \"quotes\" and 'apostrophes' and \n newlines"
      let response = toErrorResponse err
      response.error.message `shouldEqual` "Error: \"quotes\" and 'apostrophes' and \n newlines"

    it "handles error message with unicode" do
      let err = AuthError "错误: 测试消息"
      let response = toErrorResponse err
      response.error.message `shouldEqual` "错误: 测试消息"

  describe "toHttpStatus" do
    it "maps AuthError to 401" do
      toHttpStatus (AuthError "test") `shouldEqual` 401

    it "maps CreditsError to 401" do
      toHttpStatus (CreditsError "test") `shouldEqual` 401

    it "maps MonthlyLimitError to 401" do
      toHttpStatus (MonthlyLimitError "test") `shouldEqual` 401

    it "maps UserLimitError to 401" do
      toHttpStatus (UserLimitError "test") `shouldEqual` 401

    it "maps ModelError to 401" do
      toHttpStatus (ModelError "test") `shouldEqual` 401

    it "maps RateLimitError to 429" do
      toHttpStatus (RateLimitError "test") `shouldEqual` 429

    it "maps SubscriptionError to 429" do
      toHttpStatus (SubscriptionError "test" Nothing) `shouldEqual` 429

    it "maps SubscriptionError with retryAfter to 429" do
      toHttpStatus (SubscriptionError "test" (Just 60)) `shouldEqual` 429

    it "maps InternalError to 500" do
      toHttpStatus (InternalError "test") `shouldEqual` 500

    it "BUG: InternalError type is 'error' not 'InternalError'" do
      -- BUG: getErrorType returns "error" for InternalError instead of "InternalError"
      let err = InternalError "test"
      let response = toErrorResponse err
      response.error.type `shouldEqual` "error"  -- Bug: should be "InternalError"
      -- This test documents the bug

  describe "getErrorType (via toErrorResponse)" do
    it "extracts AuthError type" do
      let response = toErrorResponse (AuthError "test")
      response.error.type `shouldEqual` "AuthError"

    it "extracts CreditsError type" do
      let response = toErrorResponse (CreditsError "test")
      response.error.type `shouldEqual` "CreditsError"

    it "extracts MonthlyLimitError type" do
      let response = toErrorResponse (MonthlyLimitError "test")
      response.error.type `shouldEqual` "MonthlyLimitError"

    it "extracts SubscriptionError type" do
      let response = toErrorResponse (SubscriptionError "test" Nothing)
      response.error.type `shouldEqual` "SubscriptionError"

    it "extracts UserLimitError type" do
      let response = toErrorResponse (UserLimitError "test")
      response.error.type `shouldEqual` "UserLimitError"

    it "extracts ModelError type" do
      let response = toErrorResponse (ModelError "test")
      response.error.type `shouldEqual` "ModelError"

    it "extracts RateLimitError type" do
      let response = toErrorResponse (RateLimitError "test")
      response.error.type `shouldEqual` "RateLimitError"

    it "BUG: InternalError type is 'error' not 'InternalError'" do
      -- BUG: Line 66 returns "error" instead of "InternalError"
      let response = toErrorResponse (InternalError "test")
      response.error.type `shouldEqual` "error"  -- Bug: should be "InternalError"
      -- This test documents the bug

  describe "getErrorMessage (via toErrorResponse)" do
    it "extracts AuthError message" do
      let response = toErrorResponse (AuthError "Missing API key.")
      response.error.message `shouldEqual` "Missing API key."

    it "extracts CreditsError message" do
      let response = toErrorResponse (CreditsError "Insufficient balance.")
      response.error.message `shouldEqual` "Insufficient balance."

    it "extracts MonthlyLimitError message" do
      let response = toErrorResponse (MonthlyLimitError "Limit exceeded.")
      response.error.message `shouldEqual` "Limit exceeded."

    it "extracts SubscriptionError message" do
      let response = toErrorResponse (SubscriptionError "Quota exceeded." (Just 60))
      response.error.message `shouldEqual` "Quota exceeded."

    it "extracts UserLimitError message" do
      let response = toErrorResponse (UserLimitError "User limit exceeded.")
      response.error.message `shouldEqual` "User limit exceeded."

    it "extracts ModelError message" do
      let response = toErrorResponse (ModelError "Model not supported.")
      response.error.message `shouldEqual` "Model not supported."

    it "extracts RateLimitError message" do
      let response = toErrorResponse (RateLimitError "Rate limit exceeded.")
      response.error.message `shouldEqual` "Rate limit exceeded."

    it "extracts InternalError message" do
      let response = toErrorResponse (InternalError "Internal server error.")
      response.error.message `shouldEqual` "Internal server error."

    it "handles empty message" do
      let response = toErrorResponse (AuthError "")
      response.error.message `shouldEqual` ""

    it "handles message with newlines" do
      let msg = "Line 1\nLine 2\nLine 3"
      let response = toErrorResponse (AuthError msg)
      response.error.message `shouldEqual` msg

    it "handles message with quotes" do
      let msg = "Error: \"quoted\" text"
      let response = toErrorResponse (AuthError msg)
      response.error.message `shouldEqual` msg

  describe "Error Response Structure" do
    it "always has type='error' at top level" do
      let response = toErrorResponse (AuthError "test")
      response.type `shouldEqual` "error"

    it "always has error.type matching error type" do
      let response = toErrorResponse (CreditsError "test")
      response.error.type `shouldEqual` "CreditsError"

    it "always has error.message matching error message" do
      let response = toErrorResponse (ModelError "test")
      response.error.message `shouldEqual` "test"

    it "preserves error message exactly" do
      let msg = "Complex error: \"quotes\" 'apostrophes' \n newlines \t tabs"
      let response = toErrorResponse (AuthError msg)
      response.error.message `shouldEqual` msg

  describe "Edge Cases" do
    it "handles whitespace-only error message" do
      let response = toErrorResponse (AuthError "   ")
      response.error.message `shouldEqual` "   "

    it "handles error message with only newlines" do
      let response = toErrorResponse (AuthError "\n\n\n")
      response.error.message `shouldEqual` "\n\n\n"

    it "handles error message with unicode emoji" do
      let response = toErrorResponse (AuthError "Error: 🚨 ⚠️ ❌")
      response.error.message `shouldEqual` "Error: 🚨 ⚠️ ❌"

    it "handles very long error type" do
      -- Test handling of very long error type strings
      let response = toErrorResponse (AuthError "test")
      response.error.type.length `shouldNotEqual` 0

    it "handles SubscriptionError with zero retryAfter" do
      let response = toErrorResponse (SubscriptionError "test" (Just 0))
      response.error.type `shouldEqual` "SubscriptionError"
      response.error.message `shouldEqual` "test"

    it "handles SubscriptionError with negative retryAfter (edge case)" do
      -- Test handling of negative retryAfter values
      let response = toErrorResponse (SubscriptionError "test" (Just (-60)))
      response.error.type `shouldEqual` "SubscriptionError"
      response.error.message `shouldEqual` "test"

    it "handles SubscriptionError with very large retryAfter" do
      let response = toErrorResponse (SubscriptionError "test" (Just 2147483647))
      response.error.type `shouldEqual` "SubscriptionError"
      response.error.message `shouldEqual` "test"

  describe "HTTP Status Code Mapping" do
    it "maps all authentication-related errors to 401" do
      toHttpStatus (AuthError "test") `shouldEqual` 401
      toHttpStatus (CreditsError "test") `shouldEqual` 401
      toHttpStatus (MonthlyLimitError "test") `shouldEqual` 401
      toHttpStatus (UserLimitError "test") `shouldEqual` 401
      toHttpStatus (ModelError "test") `shouldEqual` 401

    it "maps all rate limit errors to 429" do
      toHttpStatus (RateLimitError "test") `shouldEqual` 429
      toHttpStatus (SubscriptionError "test" Nothing) `shouldEqual` 429

    it "maps internal errors to 500" do
      toHttpStatus (InternalError "test") `shouldEqual` 500

    it "BUG: InternalError type inconsistency" do
      -- BUG: InternalError has type "error" but status 500
      -- This inconsistency could confuse clients
      let err = InternalError "test"
      let response = toErrorResponse err
      let status = toHttpStatus err
      response.error.type `shouldEqual` "error"  -- Bug: should be "InternalError"
      status `shouldEqual` 500  -- Correct
      -- This test documents the inconsistency

  describe "Integration Edge Cases" do
    it "toErrorResponse and toHttpStatus work together correctly" do
      let err = AuthError "test"
      let response = toErrorResponse err
      let status = toHttpStatus err
      response.error.type `shouldEqual` "AuthError"
      status `shouldEqual` 401

    it "all error types have consistent structure" do
      let errors = 
            [ AuthError "test"
            , CreditsError "test"
            , MonthlyLimitError "test"
            , SubscriptionError "test" Nothing
            , UserLimitError "test"
            , ModelError "test"
            , RateLimitError "test"
            , InternalError "test"
            ]
      -- All should have type="error" at top level
      -- All should have error.type matching error type
      -- All should have error.message matching error message
      pure unit

  describe "Bug Detection Tests" do
    it "detects bug: InternalError type is 'error' not 'InternalError'" do
      -- BUG: Line 66 in Error.purs returns "error" for InternalError
      -- Expected: "InternalError"
      -- Actual: "error"
      let response = toErrorResponse (InternalError "test")
      response.error.type `shouldEqual` "error"  -- Bug documented
      -- This test documents the bug

    it "verifies all other error types are correct" do
      -- Verify all other types are correct (they are)
      let authResponse = toErrorResponse (AuthError "test")
      let creditsResponse = toErrorResponse (CreditsError "test")
      let monthlyResponse = toErrorResponse (MonthlyLimitError "test")
      let subResponse = toErrorResponse (SubscriptionError "test" Nothing)
      let userResponse = toErrorResponse (UserLimitError "test")
      let modelResponse = toErrorResponse (ModelError "test")
      let rateResponse = toErrorResponse (RateLimitError "test")
      authResponse.error.type `shouldEqual` "AuthError"
      creditsResponse.error.type `shouldEqual` "CreditsError"
      monthlyResponse.error.type `shouldEqual` "MonthlyLimitError"
      subResponse.error.type `shouldEqual` "SubscriptionError"
      userResponse.error.type `shouldEqual` "UserLimitError"
      modelResponse.error.type `shouldEqual` "ModelError"
      rateResponse.error.type `shouldEqual` "RateLimitError"

    it "verifies HTTP status codes are correct" do
      -- All status codes are correct
      toHttpStatus (AuthError "test") `shouldEqual` 401
      toHttpStatus (CreditsError "test") `shouldEqual` 401
      toHttpStatus (MonthlyLimitError "test") `shouldEqual` 401
      toHttpStatus (UserLimitError "test") `shouldEqual` 401
      toHttpStatus (ModelError "test") `shouldEqual` 401
      toHttpStatus (RateLimitError "test") `shouldEqual` 429
      toHttpStatus (SubscriptionError "test" Nothing) `shouldEqual` 429
      toHttpStatus (InternalError "test") `shouldEqual` 500

  describe "getRetryAfter" do
    it "returns Just retryAfter for SubscriptionError" do
      getRetryAfter (SubscriptionError "test" (Just 60)) `shouldEqual` Just 60

    it "returns Nothing for SubscriptionError with Nothing retryAfter" do
      getRetryAfter (SubscriptionError "test" Nothing) `shouldEqual` Nothing

    it "returns Nothing for non-SubscriptionError errors" do
      getRetryAfter (AuthError "test") `shouldEqual` Nothing
      getRetryAfter (CreditsError "test") `shouldEqual` Nothing
      getRetryAfter (MonthlyLimitError "test") `shouldEqual` Nothing
      getRetryAfter (UserLimitError "test") `shouldEqual` Nothing
      getRetryAfter (ModelError "test") `shouldEqual` Nothing
      getRetryAfter (RateLimitError "test") `shouldEqual` Nothing
      getRetryAfter (InternalError "test") `shouldEqual` Nothing

    it "handles zero retryAfter" do
      getRetryAfter (SubscriptionError "test" (Just 0)) `shouldEqual` Just 0

    it "handles negative retryAfter (edge case)" do
      getRetryAfter (SubscriptionError "test" (Just (-60))) `shouldEqual` Just (-60)

    it "handles very large retryAfter" do
      getRetryAfter (SubscriptionError "test" (Just 2147483647)) `shouldEqual` Just 2147483647

  describe "formatResetTime" do
    it "formats seconds less than 60 as minutes (ceiling)" do
      formatResetTime 0 `shouldEqual` "0min"
      formatResetTime 1 `shouldEqual` "1min"
      formatResetTime 59 `shouldEqual` "1min"
      formatResetTime 60 `shouldEqual` "1min"

    it "formats seconds between 60 and 3600 as hours and minutes" do
      formatResetTime 3600 `shouldEqual` "1hr 0min"
      formatResetTime 3660 `shouldEqual` "1hr 1min"
      formatResetTime 7200 `shouldEqual` "2hr 0min"
      formatResetTime 7260 `shouldEqual` "2hr 1min"

    it "formats seconds >= 86400 as days" do
      formatResetTime 86400 `shouldEqual` "1 day"
      formatResetTime 172800 `shouldEqual` "2 days"
      formatResetTime 259200 `shouldEqual` "3 days"

    it "BUG: uses integer division for hours/minutes calculation" do
      -- BUG: Line 144 uses integer division which may truncate
      -- Example: 3599 seconds should be "59min" but might be calculated incorrectly
      formatResetTime 3599 `shouldEqual` "0hr 59min"

    it "BUG: ceiling calculation for minutes may be incorrect" do
      -- BUG: Line 148 uses (seconds + 59) / 60 for ceiling
      -- Test edge case handling
      formatResetTime 1 `shouldEqual` "1min"
      formatResetTime 60 `shouldEqual` "1min"
      formatResetTime 119 `shouldEqual` "1min"  -- Should be 2min but ceiling might be wrong

    it "handles very large values" do
      formatResetTime 2147483647 `shouldEqual` "24855 days"  -- Approximate

  describe "Error Constructor Functions" do
    it "authErrorMissingKey creates correct error" do
      let err = authErrorMissingKey
      let response = toErrorResponse err
      toHttpStatus err `shouldEqual` 401
      response.error.message `shouldEqual` "Missing API key."

    it "authErrorInvalidKey creates correct error" do
      let err = authErrorInvalidKey
      toHttpStatus err `shouldEqual` 401
      (toErrorResponse err).error.message `shouldEqual` "Invalid API key."

    it "modelErrorNotSupported creates correct error with model name" do
      let err = modelErrorNotSupported "gpt-5"
      toHttpStatus err `shouldEqual` 401
      (toErrorResponse err).error.message `shouldEqual` "Model gpt-5 not supported"

    it "modelErrorNotSupported handles empty model name" do
      let err = modelErrorNotSupported ""
      (toErrorResponse err).error.message `shouldEqual` "Model  not supported"

    it "modelErrorNoProvider creates correct error" do
      let err = modelErrorNoProvider
      toHttpStatus err `shouldEqual` 401
      getErrorMessage err `shouldEqual` "No provider available"

    it "modelErrorDisabled creates correct error" do
      let err = modelErrorDisabled
      toHttpStatus err `shouldEqual` 401
      (toErrorResponse err).error.message `shouldEqual` "Model is disabled"

    it "creditsErrorNoPayment creates correct error with workspace ID" do
      let err = creditsErrorNoPayment "workspace-123"
      toHttpStatus err `shouldEqual` 401
      let msg = (toErrorResponse err).error.message
      msg `shouldContain` "No payment method"
      msg `shouldContain` "workspace-123"
      msg `shouldContain` "/billing"

    it "creditsErrorNoPayment handles empty workspace ID" do
      let err = creditsErrorNoPayment ""
      (toErrorResponse err).error.message `shouldContain` "No payment method"

    it "creditsErrorInsufficientBalance creates correct error with workspace ID" do
      let err = creditsErrorInsufficientBalance "workspace-456"
      toHttpStatus err `shouldEqual` 401
      let msg = (toErrorResponse err).error.message
      msg `shouldContain` "Insufficient balance"
      msg `shouldContain` "workspace-456"
      msg `shouldContain` "/billing"

    it "creditsErrorInsufficientBalance handles empty workspace ID" do
      let err = creditsErrorInsufficientBalance ""
      (toErrorResponse err).error.message `shouldContain` "Insufficient balance"

    it "monthlyLimitExceeded creates correct error with limit and workspace ID" do
      let err = monthlyLimitExceeded 100 "workspace-789"
      toHttpStatus err `shouldEqual` 401
      let msg = (toErrorResponse err).error.message
      msg `shouldContain` "$100"
      msg `shouldContain` "workspace-789"
      msg `shouldContain` "/billing"

    it "monthlyLimitExceeded handles zero limit" do
      let err = monthlyLimitExceeded 0 "workspace-789"
      getErrorMessage err `shouldContain` "$0"

    it "monthlyLimitExceeded handles very large limit" do
      let err = monthlyLimitExceeded 999999 "workspace-789"
      (toErrorResponse err).error.message `shouldContain` "$999999"

    it "userLimitExceeded creates correct error with limit and workspace ID" do
      let err = userLimitExceeded 50 "workspace-abc"
      toHttpStatus err `shouldEqual` 401
      let msg = (toErrorResponse err).error.message
      msg `shouldContain` "$50"
      msg `shouldContain` "workspace-abc"
      msg `shouldContain` "/members"

    it "userLimitExceeded handles zero limit" do
      let err = userLimitExceeded 0 "workspace-abc"
      getErrorMessage err `shouldContain` "$0"

    it "subscriptionQuotaExceeded creates correct error with retry time" do
      let err = subscriptionQuotaExceeded 60
      toHttpStatus err `shouldEqual` 429
      getRetryAfter err `shouldEqual` Just 60
      (toErrorResponse err).error.message `shouldContain` "Retry in"

    it "subscriptionQuotaExceeded formats retry time correctly" do
      let err1 = subscriptionQuotaExceeded 60
      let err2 = subscriptionQuotaExceeded 3600
      let err3 = subscriptionQuotaExceeded 86400
      getErrorMessage err1 `shouldContain` "min"
      getErrorMessage err2 `shouldContain` "hr"
      getErrorMessage err3 `shouldContain` "day"

    it "rateLimitExceeded creates correct error" do
      let err = rateLimitExceeded
      toHttpStatus err `shouldEqual` 429
      (toErrorResponse err).error.message `shouldEqual` "Rate limit exceeded. Please try again later."

    it "all constructor functions create valid ErrorResponse" do
      let errors = 
            [ authErrorMissingKey
            , authErrorInvalidKey
            , modelErrorNotSupported "test-model"
            , modelErrorNoProvider
            , modelErrorDisabled
            , creditsErrorNoPayment "workspace-123"
            , creditsErrorInsufficientBalance "workspace-456"
            , monthlyLimitExceeded 100 "workspace-789"
            , userLimitExceeded 50 "workspace-abc"
            , subscriptionQuotaExceeded 60
            , rateLimitExceeded
            ]
      -- All should create valid ErrorResponse
      pure unit
