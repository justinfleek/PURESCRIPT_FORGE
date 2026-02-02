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
import Effect.Unsafe (unsafePerformEffect)
import Effect (Effect)

import Data.Maybe (Maybe(..), fromMaybe)

-- | FFI: Get current timestamp as ISO string
foreign import getCurrentTimestampImpl :: Effect String

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
networkUnreachableCode :: Int
networkUnreachableCode = 1001

connectionTimeoutCode :: Int
connectionTimeoutCode = 1002

connectionRefusedCode :: Int
connectionRefusedCode = 1003

sslErrorCode :: Int
sslErrorCode = 1004

dnsFailureCode :: Int
dnsFailureCode = 1005

-- | Authentication Errors (2xxx)
invalidApiKeyCode :: Int
invalidApiKeyCode = 2001

apiKeyExpiredCode :: Int
apiKeyExpiredCode = 2002

insufficientPermissionsCode :: Int
insufficientPermissionsCode = 2003

sessionExpiredCode :: Int
sessionExpiredCode = 2004

tokenInvalidCode :: Int
tokenInvalidCode = 2005

-- | Rate Limit Errors (3xxx)
rateLimitedRequestsCode :: Int
rateLimitedRequestsCode = 3001

rateLimitedTokensCode :: Int
rateLimitedTokensCode = 3002

dailyLimitReachedCode :: Int
dailyLimitReachedCode = 3003

balanceDepletedCode :: Int
balanceDepletedCode = 3004

-- | Validation Errors (4xxx)
invalidJsonCode :: Int
invalidJsonCode = 4001

missingFieldCode :: Int
missingFieldCode = 4002

invalidTypeCode :: Int
invalidTypeCode = 4003

valueOutOfRangeCode :: Int
valueOutOfRangeCode = 4004

messageTooLargeCode :: Int
messageTooLargeCode = 4005

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
createError category code message userMessage retryable recovery details =
  { category
  , code
  , message
  , userMessage
  , retryable
  , recovery
  , details
  , timestamp: unsafePerformEffect getCurrentTimestampImpl
  }

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
networkUnreachableErr :: String -> BridgeError
networkUnreachableErr details = createError NetworkError networkUnreachableCode
  "Network unreachable"
  "Unable to reach Venice API. Please check your internet connection."
  true
  (RetryWithBackoff 3)
  (Just details)

connectionTimeout :: String -> BridgeError
connectionTimeout details = createError NetworkError connectionTimeoutCode
  "Connection timeout"
  "Request timed out. Please try again."
  true
  (RetryWithBackoff 1)
  (Just details)

-- | Authentication error constructors
invalidApiKey :: String -> BridgeError
invalidApiKey details = createError AuthenticationError invalidApiKeyCode
  "Invalid API key"
  "API key is invalid. Please check your settings."
  false
  StopAndAlert
  (Just details)

sessionExpired :: String -> BridgeError
sessionExpired details = createError AuthenticationError sessionExpiredCode
  "Session expired"
  "Your session has expired. Please re-authenticate."
  false
  StopAndAlert
  (Just details)

-- | Rate limit error constructors
rateLimited :: String -> Int -> BridgeError -- retryAfter seconds
rateLimited operation retryAfter = createError RateLimitError rateLimitedRequestsCode
  ("Rate limit exceeded for " <> operation)
  ("Too many requests. Please wait " <> show retryAfter <> " seconds.")
  true
  (RetryWithBackoff 1)
  (Just operation)

balanceDepleted :: String -> BridgeError
balanceDepleted details = createError RateLimitError balanceDepletedCode
  "Balance depleted"
  "Your Diem balance has been depleted. Wait for daily reset."
  false
  StopAndAlert
  (Just details)

-- | Validation error constructors
invalidJson :: String -> BridgeError
invalidJson details = createError ValidationError invalidJsonCode
  "Invalid JSON format"
  "Invalid request format. Please check your input."
  false
  FixAndRetry
  (Just details)

missingField :: String -> BridgeError
missingField field = createError ValidationError missingFieldCode
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
