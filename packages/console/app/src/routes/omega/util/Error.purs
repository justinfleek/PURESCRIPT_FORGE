-- | Omega API Error Types
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/error.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Omega.Util.Error
  ( OmegaError(..)
  , ErrorResponse(..)
  , toErrorResponse
  , toHttpStatus
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- | Error types for Omega API
data OmegaError
  = AuthError String
  | CreditsError String
  | MonthlyLimitError String
  | SubscriptionError String (Maybe Int)  -- message and optional retryAfter
  | UserLimitError String
  | ModelError String
  | RateLimitError String
  | InternalError String

derive instance eqOmegaError :: Eq OmegaError

instance showOmegaError :: Show OmegaError where
  show (AuthError msg) = "AuthError: " <> msg
  show (CreditsError msg) = "CreditsError: " <> msg
  show (MonthlyLimitError msg) = "MonthlyLimitError: " <> msg
  show (SubscriptionError msg _) = "SubscriptionError: " <> msg
  show (UserLimitError msg) = "UserLimitError: " <> msg
  show (ModelError msg) = "ModelError: " <> msg
  show (RateLimitError msg) = "RateLimitError: " <> msg
  show (InternalError msg) = "InternalError: " <> msg

-- | Error response structure
type ErrorResponse =
  { type :: String
  , error ::
      { type :: String
      , message :: String
      }
  }

-- | Convert error to response format
toErrorResponse :: OmegaError -> ErrorResponse
toErrorResponse err =
  { type: "error"
  , error:
      { type: getErrorType err
      , message: getErrorMessage err
      }
  }

-- | Get error type string
getErrorType :: OmegaError -> String
getErrorType (AuthError _) = "AuthError"
getErrorType (CreditsError _) = "CreditsError"
getErrorType (MonthlyLimitError _) = "MonthlyLimitError"
getErrorType (SubscriptionError _ _) = "SubscriptionError"
getErrorType (UserLimitError _) = "UserLimitError"
getErrorType (ModelError _) = "ModelError"
getErrorType (RateLimitError _) = "RateLimitError"
getErrorType (InternalError _) = "error"

-- | Get error message
getErrorMessage :: OmegaError -> String
getErrorMessage (AuthError msg) = msg
getErrorMessage (CreditsError msg) = msg
getErrorMessage (MonthlyLimitError msg) = msg
getErrorMessage (SubscriptionError msg _) = msg
getErrorMessage (UserLimitError msg) = msg
getErrorMessage (ModelError msg) = msg
getErrorMessage (RateLimitError msg) = msg
getErrorMessage (InternalError msg) = msg

-- | Map error to HTTP status code
toHttpStatus :: OmegaError -> Int
toHttpStatus (AuthError _) = 401
toHttpStatus (CreditsError _) = 401
toHttpStatus (MonthlyLimitError _) = 401
toHttpStatus (UserLimitError _) = 401
toHttpStatus (ModelError _) = 401
toHttpStatus (RateLimitError _) = 429
toHttpStatus (SubscriptionError _ _) = 429
toHttpStatus (InternalError _) = 500

-- | Get retry-after header value if applicable
getRetryAfter :: OmegaError -> Maybe Int
getRetryAfter (SubscriptionError _ retryAfter) = retryAfter
getRetryAfter _ = Nothing

-- | Common error messages
authErrorMissingKey :: OmegaError
authErrorMissingKey = AuthError "Missing API key."

authErrorInvalidKey :: OmegaError
authErrorInvalidKey = AuthError "Invalid API key."

modelErrorNotSupported :: String -> OmegaError
modelErrorNotSupported model = ModelError $ "Model " <> model <> " not supported"

modelErrorNoProvider :: OmegaError
modelErrorNoProvider = ModelError "No provider available"

modelErrorDisabled :: OmegaError
modelErrorDisabled = ModelError "Model is disabled"

creditsErrorNoPayment :: String -> OmegaError
creditsErrorNoPayment workspaceId = CreditsError $
  "No payment method. Add a payment method here: https://opencode.ai/workspace/" <> workspaceId <> "/billing"

creditsErrorInsufficientBalance :: String -> OmegaError
creditsErrorInsufficientBalance workspaceId = CreditsError $
  "Insufficient balance. Manage your billing here: https://opencode.ai/workspace/" <> workspaceId <> "/billing"

monthlyLimitExceeded :: Int -> String -> OmegaError
monthlyLimitExceeded limit workspaceId = MonthlyLimitError $
  "Your workspace has reached its monthly spending limit of $" <> show limit <> ". Manage your limits here: https://opencode.ai/workspace/" <> workspaceId <> "/billing"

userLimitExceeded :: Int -> String -> OmegaError
userLimitExceeded limit workspaceId = UserLimitError $
  "You have reached your monthly spending limit of $" <> show limit <> ". Manage your limits here: https://opencode.ai/workspace/" <> workspaceId <> "/members"

subscriptionQuotaExceeded :: Int -> OmegaError
subscriptionQuotaExceeded resetInSec = SubscriptionError
  ("Subscription quota exceeded. Retry in " <> formatResetTime resetInSec <> ".")
  (Just resetInSec)

rateLimitExceeded :: OmegaError
rateLimitExceeded = RateLimitError "Rate limit exceeded. Please try again later."

-- | Format reset time for display
formatResetTime :: Int -> String
formatResetTime seconds
  | seconds >= 86400 =
      let days = seconds / 86400
      in show days <> (if days > 1 then " days" else " day")
  | seconds >= 3600 =
      let
        hours = seconds / 3600
        minutes = (seconds `mod` 3600) / 60
      in
        show hours <> "hr " <> show minutes <> "min"
  | otherwise =
      let minutes = (seconds + 59) / 60  -- ceiling
      in show minutes <> "min"
