-- | Error Taxonomy - Categorized error types for the bridge server
module Bridge.Error.Taxonomy where

import Prelude
import Data.Maybe (Maybe(..))

-- | Error category
data ErrorCategory
  = NetworkError
  | AuthenticationError
  | RateLimitError
  | ValidationError
  | ServerError
  | ClientError
  | DatabaseError
  | ExternalServiceError

derive instance eqErrorCategory :: Eq ErrorCategory

instance showErrorCategory :: Show ErrorCategory where
  show NetworkError = "NetworkError"
  show AuthenticationError = "AuthenticationError"
  show RateLimitError = "RateLimitError"
  show ValidationError = "ValidationError"
  show ServerError = "ServerError"
  show ClientError = "ClientError"
  show DatabaseError = "DatabaseError"
  show ExternalServiceError = "ExternalServiceError"

-- | Recovery strategy
data RecoveryStrategy
  = RetryWithBackoff Int
  | FixAndRetry
  | StopAndAlert
  | NoRecovery

derive instance eqRecoveryStrategy :: Eq RecoveryStrategy

-- | Bridge error with categorization and recovery
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

-- | Error code constants
foreign import networkUnreachableCode :: Int
foreign import connectionTimeoutCode :: Int
foreign import connectionRefusedCode :: Int
foreign import sslErrorCode :: Int
foreign import dnsFailureCode :: Int
foreign import invalidApiKeyCode :: Int
foreign import apiKeyExpiredCode :: Int
foreign import insufficientPermissionsCode :: Int
foreign import sessionExpiredCode :: Int
foreign import tokenInvalidCode :: Int
foreign import rateLimitedRequestsCode :: Int
foreign import rateLimitedTokensCode :: Int
foreign import dailyLimitReachedCode :: Int
foreign import balanceDepletedCode :: Int
foreign import invalidJsonCode :: Int
foreign import missingFieldCode :: Int
foreign import invalidTypeCode :: Int
foreign import valueOutOfRangeCode :: Int
foreign import messageTooLargeCode :: Int
foreign import getCurrentTimestamp :: String

-- | Create a categorized error
createError :: ErrorCategory -> Int -> String -> String -> Boolean -> RecoveryStrategy -> Maybe String -> BridgeError
createError category code message userMessage retryable recovery details =
  { category
  , code
  , message
  , userMessage
  , retryable
  , recovery
  , details
  , timestamp: getCurrentTimestamp
  }

-- | Check if error is retryable
isRetryable :: BridgeError -> Boolean
isRetryable err = err.retryable

-- | Get recovery strategy
getRecoveryStrategy :: BridgeError -> RecoveryStrategy
getRecoveryStrategy err = err.recovery

-- | Network unreachable error
networkUnreachable :: String -> BridgeError
networkUnreachable details = createError NetworkError networkUnreachableCode
  "Network unreachable" "Unable to reach the server. Check your connection."
  true (RetryWithBackoff 3) (Just details)

-- | Connection timeout error
connectionTimeout :: String -> BridgeError
connectionTimeout details = createError NetworkError connectionTimeoutCode
  "Connection timed out" "The request took too long. Please try again."
  true (RetryWithBackoff 1) (Just details)

-- | Invalid API key error
invalidApiKey :: String -> BridgeError
invalidApiKey details = createError AuthenticationError invalidApiKeyCode
  "Invalid API key" "Your API key is invalid. Please check your settings."
  false StopAndAlert (Just details)

-- | Session expired error
sessionExpired :: String -> BridgeError
sessionExpired details = createError AuthenticationError sessionExpiredCode
  "Session expired" "Your session has expired. Please log in again."
  false StopAndAlert (Just details)

-- | Rate limited error
rateLimited :: String -> Int -> BridgeError
rateLimited details retryAfter = createError RateLimitError rateLimitedRequestsCode
  "Rate limited" "Too many requests. Please wait before trying again."
  true (RetryWithBackoff retryAfter) (Just details)

-- | Balance depleted error
balanceDepleted :: String -> BridgeError
balanceDepleted details = createError RateLimitError balanceDepletedCode
  "Balance depleted" "Your balance is depleted. Please add funds."
  false StopAndAlert (Just details)

-- | Invalid JSON error
invalidJson :: String -> BridgeError
invalidJson details = createError ValidationError invalidJsonCode
  "Invalid JSON" "The request contained invalid JSON."
  false FixAndRetry (Just details)

-- | Missing field error
missingField :: String -> BridgeError
missingField details = createError ValidationError missingFieldCode
  "Missing required field" "A required field is missing from the request."
  false FixAndRetry (Just details)

-- | Internal server error
internalError :: String -> BridgeError
internalError details = createError ServerError 5001
  "Internal server error" "An unexpected error occurred. Please try again."
  true (RetryWithBackoff 2) (Just details)

-- | Database error
databaseError :: String -> BridgeError
databaseError details = createError DatabaseError 6001
  "Database error" "A database error occurred."
  true (RetryWithBackoff 2) (Just details)

-- | Venice API error
veniceApiError :: String -> BridgeError
veniceApiError details = createError ExternalServiceError 7001
  "Venice API error" "The Venice AI service returned an error."
  true (RetryWithBackoff 3) (Just details)

-- | Lean LSP error
leanLspError :: String -> BridgeError
leanLspError details = createError ExternalServiceError 8001
  "Lean LSP error" "The Lean proof assistant returned an error."
  false FixAndRetry (Just details)
