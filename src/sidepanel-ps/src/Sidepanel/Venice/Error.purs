-- | Venice Error Handling - Error Types and Recovery Strategies
-- |
-- | **What:** Defines Venice API error types, error handling strategies, and recovery
-- |         mechanisms for various error scenarios (rate limits, network errors, auth errors).
-- | **Why:** Provides robust error handling for Venice API interactions, ensuring the
-- |         application gracefully handles errors and recovers when possible.
-- | **How:** Defines error types, implements retry strategies with exponential backoff,
-- |         and provides error-to-alert conversion for user feedback.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.Api.Types`: JsonRpcError type
-- | - `Sidepanel.State.RateLimit`: Rate limit state for rate limit errors
-- |
-- | **Mathematical Foundation:**
-- | - **Retry Strategy:** Exponential backoff: `delay = baseDelay * (2 ^ attempt)`
-- | - **Max Retries:** Configurable maximum retry attempts (default 3)
-- | - **Retryable Errors:** Only certain error types are retryable (network, rate limit)
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Venice.Error as VeniceError
-- |
-- | -- Handle error
-- | case VeniceError.parseError jsonRpcError of
-- |   Just (VeniceError.RateLimitError retryAfter) -> HandleRateLimit retryAfter
-- |   Just (VeniceError.NetworkError) -> RetryWithBackoff
-- |   Just (VeniceError.AuthError) -> ShowAuthError
-- |   Nothing -> ShowGenericError
-- | ```
-- |
-- | Based on spec 17-VENICE-ERROR-HANDLING.md
module Sidepanel.Venice.Error where

import Prelude
import Data.Maybe (Maybe(..))
import Sidepanel.Api.Types (JsonRpcError)

-- | Venice error types - Categories of Venice API errors
-- |
-- | **Purpose:** Represents different types of errors that can occur when interacting
-- |             with Venice API, each with different recovery strategies.
data VeniceError
  = RateLimitError Number  -- retryAfterSeconds
  | NetworkError String    -- error message
  | AuthError String       -- error message
  | ValidationError String -- error message
  | ServerError Int String -- status code, error message
  | UnknownError String   -- error message

derive instance eqVeniceError :: Eq VeniceError

-- | Error recovery strategy - Strategy for handling and recovering from errors
-- |
-- | **Purpose:** Defines how to recover from different error types.
data RecoveryStrategy
  = RetryWithBackoff Int Number  -- maxRetries, baseDelaySeconds
  | RetryAfter Number            -- retryAfterSeconds
  | ShowError                    -- Show error, no retry
  | RefreshAuth                  -- Refresh authentication
  | NoRecovery                   -- Fatal error, no recovery

derive instance eqRecoveryStrategy :: Eq RecoveryStrategy

-- | Parse JSON-RPC error to Venice error - Convert JsonRpcError to VeniceError
-- |
-- | **Purpose:** Parses a JSON-RPC error from Venice API and converts it to a
-- |             VeniceError type for handling.
-- | **Parameters:**
-- | - `error`: JSON-RPC error from API
-- | **Returns:** Maybe VeniceError (Nothing if error format is unknown)
-- | **Side Effects:** None (pure function)
-- |
-- | **Error Code Mapping:**
-- | - 429: RateLimitError
-- | - 401, 403: AuthError
-- | - 400, 422: ValidationError
-- | - 500-599: ServerError
-- | - Others: NetworkError or UnknownError
parseError :: JsonRpcError -> Maybe VeniceError
parseError error = case error.code of
  429 ->
    -- Rate limit error - extract retryAfter from data
    -- Note: JsonRpcError.data is Maybe (Record String), so we'd need to parse it
    -- For now, use default 30 seconds
    Just (RateLimitError 30.0)
  
  401 -> Just (AuthError error.message)
  403 -> Just (AuthError error.message)
  
  400 -> Just (ValidationError error.message)
  422 -> Just (ValidationError error.message)
  
  code | code >= 500 && code < 600 ->
    Just (ServerError code error.message)
  
  _ ->
    -- Check error message for network errors
    if String.contains (String.Pattern "network") (String.toLower error.message) ||
       String.contains (String.Pattern "timeout") (String.toLower error.message) ||
       String.contains (String.Pattern "connection") (String.toLower error.message) then
      Just (NetworkError error.message)
    else
      Just (UnknownError error.message)

-- | Get recovery strategy - Determine recovery strategy for error
-- |
-- | **Purpose:** Determines the appropriate recovery strategy for a Venice error.
-- | **Parameters:**
-- | - `error`: Venice error
-- | **Returns:** RecoveryStrategy for the error
-- | **Side Effects:** None (pure function)
-- |
-- | **Strategy Mapping:**
-- | - RateLimitError: RetryAfter (use retryAfterSeconds)
-- | - NetworkError: RetryWithBackoff (3 retries, exponential backoff)
-- | - AuthError: RefreshAuth (refresh authentication)
-- | - ValidationError: ShowError (user error, no retry)
-- | - ServerError: RetryWithBackoff (2 retries, longer backoff)
-- | - UnknownError: ShowError (unknown error, no retry)
getRecoveryStrategy :: VeniceError -> RecoveryStrategy
getRecoveryStrategy = case _ of
  RateLimitError retryAfter ->
    RetryAfter retryAfter
  
  NetworkError _ ->
    RetryWithBackoff 3 1.0  -- 3 retries, 1s base delay
  
  AuthError _ ->
    RefreshAuth
  
  ValidationError _ ->
    ShowError
  
  ServerError code _ ->
    if code >= 500 && code < 503 then
      RetryWithBackoff 2 2.0  -- 2 retries, 2s base delay for 5xx errors
    else
      ShowError
  
  UnknownError _ ->
    ShowError

-- | Is retryable - Check if error is retryable
-- |
-- | **Purpose:** Determines if an error can be retried (network errors, rate limits,
-- |             temporary server errors).
-- | **Parameters:**
-- | - `error`: Venice error
-- | **Returns:** True if error is retryable, false otherwise
isRetryable :: VeniceError -> Boolean
isRetryable = case _ of
  RateLimitError _ -> true
  NetworkError _ -> true
  ServerError code _ -> code >= 500 && code < 503
  _ -> false

-- | Get error message - Get user-friendly error message
-- |
-- | **Purpose:** Converts a Venice error to a user-friendly error message.
-- | **Parameters:**
-- | - `error`: Venice error
-- | **Returns:** User-friendly error message string
getErrorMessage :: VeniceError -> String
getErrorMessage = case _ of
  RateLimitError retryAfter ->
    "Rate limit exceeded. Retrying in " <> show (round retryAfter) <> " seconds..."
  
  NetworkError msg ->
    "Network error: " <> msg <> ". Retrying..."
  
  AuthError msg ->
    "Authentication error: " <> msg <> ". Please check your API key."
  
  ValidationError msg ->
    "Invalid request: " <> msg
  
  ServerError code msg ->
    "Server error (" <> show code <> "): " <> msg
  
  UnknownError msg ->
    "Error: " <> msg

-- | Calculate retry delay - Calculate delay for retry attempt
-- |
-- | **Purpose:** Calculates the delay before retrying based on attempt number and
-- |             base delay (exponential backoff).
-- | **Parameters:**
-- | - `attempt`: Retry attempt number (0-indexed)
-- | - `baseDelaySeconds`: Base delay in seconds
-- | **Returns:** Delay in seconds
-- | **Side Effects:** None (pure function)
-- |
-- | **Formula:** `delay = baseDelay * (2 ^ attempt)`
calculateRetryDelay :: Int -> Number -> Number
calculateRetryDelay attempt baseDelaySeconds =
  baseDelaySeconds * Math.pow 2.0 (Int.toNumber attempt)
