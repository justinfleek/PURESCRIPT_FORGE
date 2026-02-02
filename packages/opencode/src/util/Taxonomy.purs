-- | Error Taxonomy - Comprehensive Error Classification System
-- |
-- | **What:** Defines all error types, codes, categories, and recovery strategies
-- |         for the Bridge Server. Provides structured error handling with
-- |         explicit error codes and user-friendly messages.
-- | **Why:** Ensures consistent error handling across all layers. Enables proper
-- |         error recovery, user messaging, and debugging. Prevents error leakage.
-- | **How:** Defines error categories (Network, Auth, RateLimit, Validation, etc.)
-- |         with specific error codes. Each error has recovery strategy and user message.
-- |
-- | **Dependencies:**
-- | - `Bridge.FFI.Node.Pino`: Structured logging
-- |
-- | **Mathematical Foundation:**
-- | - **Error Categories:** Partition of all possible errors into disjoint sets
-- | - **Error Codes:** Unique integer codes per error type
-- | - **Recovery Strategy:** Function from error to recovery action
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Bridge.Error.Taxonomy as Error
-- |
-- | -- Create error
-- | err <- Error.createError Error.NetworkError Error.NETWORK_UNREACHABLE "Unable to reach Venice API"
-- |
-- | -- Check if retryable
-- | if Error.isRetryable err then
-- |   -- Retry with backoff
-- | else
-- |   -- Handle terminal error
-- | ```
module Bridge.Error.Taxonomy where

import Prelude
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Bridge.FFI.Node.Pino (Logger)

-- | Error category
data ErrorCategory =
  NetworkError
  | AuthenticationError
  | RateLimitError
  | ValidationError
  | ServerError
  | ClientError
  | DatabaseError
  | ExternalServiceError

derive instance eqErrorCategory :: Eq ErrorCategory

-- | Error code constants
-- | Network Errors (1xxx)
foreign import NETWORK_UNREACHABLE :: Int
foreign import CONNECTION_TIMEOUT :: Int
foreign import CONNECTION_REFUSED :: Int
foreign import SSL_ERROR :: Int
foreign import DNS_FAILURE :: Int

-- | Authentication Errors (2xxx)
foreign import INVALID_API_KEY :: Int
foreign import API_KEY_EXPIRED :: Int
foreign import INSUFFICIENT_PERMISSIONS :: Int
foreign import SESSION_EXPIRED :: Int
foreign import TOKEN_INVALID :: Int

-- | Rate Limit Errors (3xxx)
foreign import RATE_LIMITED_REQUESTS :: Int
foreign import RATE_LIMITED_TOKENS :: Int
foreign import DAILY_LIMIT_REACHED :: Int
foreign import BALANCE_DEPLETED :: Int

-- | Validation Errors (4xxx)
foreign import INVALID_JSON :: Int
foreign import MISSING_FIELD :: Int
foreign import INVALID_TYPE :: Int
foreign import VALUE_OUT_OF_RANGE :: Int
foreign import MESSAGE_TOO_LARGE :: Int

-- | Error data structure
type BridgeError =
  { category :: ErrorCategory
  , code :: Int
  , message :: String
  , userMessage :: String
  , retryable :: Boolean
  , recovery :: RecoveryStrategy
  , details :: Maybe String
  , timestamp :: String
  }

-- | Recovery strategy
data RecoveryStrategy =
  RetryWithBackoff Int -- Retry with exponential backoff (max retries)
  | FixAndRetry -- Fix the issue and retry
  | StopAndAlert -- Stop operation and alert user
  | NoRecovery -- Terminal error, no recovery possible

derive instance eqRecoveryStrategy :: Eq RecoveryStrategy

-- | Create error
-- |
-- | **Purpose:** Creates a structured error with category, code, and recovery strategy.
-- | **Parameters:**
-- | - `category`: Error category
-- | - `code`: Error code
-- | - `message`: Technical error message
-- | - `userMessage`: User-friendly error message
-- | - `retryable`: Whether error is retryable
-- | - `recovery`: Recovery strategy
-- | - `details`: Optional error details
-- | **Returns:** BridgeError instance
createError :: ErrorCategory -> Int -> String -> String -> Boolean -> RecoveryStrategy -> Maybe String -> BridgeError
createError category code message userMessage retryable recovery details = do
  { category
  , code
  , message
  , userMessage
  , retryable
  , recovery
  , details
  , timestamp: getCurrentTimestamp()
  }
  where
    foreign import getCurrentTimestamp :: String

-- | Check if error is retryable
-- |
-- | **Purpose:** Determines if error can be retried.
-- | **Parameters:**
-- | - `error`: BridgeError instance
-- | **Returns:** True if retryable
isRetryable :: BridgeError -> Boolean
isRetryable error = error.retryable

-- | Get recovery action
-- |
-- | **Purpose:** Extracts recovery strategy from error.
-- | **Parameters:**
-- | - `error`: BridgeError instance
-- | **Returns:** Recovery strategy
getRecoveryStrategy :: BridgeError -> RecoveryStrategy
getRecoveryStrategy error = error.recovery

-- | Network error constructors
networkUnreachable :: String -> BridgeError
networkUnreachable details = createError NetworkError NETWORK_UNREACHABLE
  "Network unreachable"
  "Unable to reach Venice API. Please check your internet connection."
  true
  (RetryWithBackoff 3)
  (Just details)

connectionTimeout :: String -> BridgeError
connectionTimeout details = createError NetworkError CONNECTION_TIMEOUT
  "Connection timeout"
  "Request timed out. Please try again."
  true
  (RetryWithBackoff 1)
  (Just details)

-- | Authentication error constructors
invalidApiKey :: String -> BridgeError
invalidApiKey details = createError AuthenticationError INVALID_API_KEY
  "Invalid API key"
  "API key is invalid. Please check your settings."
  false
  StopAndAlert
  (Just details)

sessionExpired :: String -> BridgeError
sessionExpired details = createError AuthenticationError SESSION_EXPIRED
  "Session expired"
  "Your session has expired. Please re-authenticate."
  false
  StopAndAlert
  (Just details)

-- | Rate limit error constructors
rateLimited :: String -> Int -> BridgeError -- retryAfter seconds
rateLimited operation retryAfter = createError RateLimitError RATE_LIMITED_REQUESTS
  ("Rate limit exceeded for " <> operation)
  ("Too many requests. Please wait " <> show retryAfter <> " seconds.")
  true
  (RetryWithBackoff 1)
  (Just operation)

balanceDepleted :: String -> BridgeError
balanceDepleted details = createError RateLimitError BALANCE_DEPLETED
  "Balance depleted"
  "Your Diem balance has been depleted. Wait for daily reset."
  false
  StopAndAlert
  (Just details)

-- | Validation error constructors
invalidJson :: String -> BridgeError
invalidJson details = createError ValidationError INVALID_JSON
  "Invalid JSON format"
  "Invalid request format. Please check your input."
  false
  FixAndRetry
  (Just details)

missingField :: String -> BridgeError
missingField field = createError ValidationError MISSING_FIELD
  ("Required field missing: " <> field)
  ("Missing required field: " <> field)
  false
  FixAndRetry
  (Just field)

-- | Server error constructors
internalError :: String -> BridgeError
internalError details = createError ServerError 5001
  "Internal server error"
  "An internal error occurred. Please try again later."
  true
  (RetryWithBackoff 2)
  (Just details)

-- | Database error constructors
databaseError :: String -> BridgeError
databaseError details = createError DatabaseError 6001
  "Database error"
  "Database operation failed. Please try again."
  true
  (RetryWithBackoff 2)
  (Just details)

-- | External service error constructors
veniceApiError :: String -> BridgeError
veniceApiError details = createError ExternalServiceError 7001
  "Venice API error"
  "Venice API returned an error. Please try again."
  true
  (RetryWithBackoff 3)
  (Just details)

leanLspError :: String -> BridgeError
leanLspError details = createError ExternalServiceError 8001
  "Lean LSP error"
  "Lean LSP returned an error. Please check your code."
  false
  FixAndRetry
  (Just details)
