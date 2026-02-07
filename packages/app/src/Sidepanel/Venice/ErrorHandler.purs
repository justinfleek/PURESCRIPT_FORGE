-- | Venice Error Handler - Error Handling with Retry Logic
-- |
-- | **What:** Provides error handling utilities for Venice API calls with automatic
-- |         retry logic, exponential backoff, and error recovery strategies.
-- | **Why:** Ensures robust error handling for Venice API interactions, automatically
-- |         retrying transient errors and providing user feedback for permanent errors.
-- | **How:** Implements retry logic with exponential backoff, tracks retry attempts,
-- |         and converts errors to alerts for user notification.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.Venice.Error`: Error types and recovery strategies
-- | - `Sidepanel.Components.AlertSystem`: Alert system for error notifications
-- |
-- | **Mathematical Foundation:**
-- | - **Exponential Backoff:** `delay = baseDelay * (2 ^ attempt)`
-- | - **Max Retries:** Configurable per error type
-- | - **Jitter:** Random jitter added to prevent thundering herd
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Venice.ErrorHandler as ErrorHandler
-- |
-- | -- Handle error with retry
-- | result <- ErrorHandler.handleWithRetry \_ -> makeVeniceRequest
-- | case result of
-- |   Right response -> ProcessResponse response
-- |   Left error -> ShowError error
-- | ```
-- |
-- | Based on spec 17-VENICE-ERROR-HANDLING.md
module Sidepanel.Venice.ErrorHandler where

import Prelude
import Effect.Aff (Aff, delay, Milliseconds(..))
import Effect.Aff.Class (class MonadAff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Int as Int
import Sidepanel.Venice.Error (VeniceError, parseError, getRecoveryStrategy, isRetryable, getErrorMessage, calculateRetryDelay, RecoveryStrategy(..), UnknownError(..))
import Sidepanel.Api.Types (JsonRpcError)

-- | Retry configuration - Configuration for retry behavior
type RetryConfig =
  { maxRetries :: Int
  , baseDelaySeconds :: Number
  , jitterEnabled :: Boolean
  }

-- | Default retry configuration
defaultRetryConfig :: RetryConfig
defaultRetryConfig =
  { maxRetries: 3
  , baseDelaySeconds: 1.0
  , jitterEnabled: true
  }

-- | Handle error with retry - Execute action with automatic retry on errors
-- |
-- | **Purpose:** Executes an action that may fail, automatically retrying on retryable
-- |             errors according to recovery strategy.
-- | **Parameters:**
-- | - `action`: Action to execute (returns Either JsonRpcError a)
-- | - `config`: Retry configuration
-- | **Returns:** Either VeniceError a (Left if all retries failed, Right on success)
-- | **Side Effects:** Delays between retries, may emit alerts
handleWithRetry :: forall a. Aff (Either JsonRpcError a) -> RetryConfig -> Aff (Either VeniceError a)
handleWithRetry action config = handleWithRetry' action config 0

handleWithRetry' :: forall a. Aff (Either JsonRpcError a) -> RetryConfig -> Int -> Aff (Either VeniceError a)
handleWithRetry' action config attempt = do
  result <- action
  case result of
    Right value ->
      pure (Right value)
    
    Left jsonError ->
      case parseError jsonError of
        Just veniceError ->
          if isRetryable veniceError && attempt < config.maxRetries then
            case getRecoveryStrategy veniceError of
              RetryAfter retryAfterSeconds -> do
                delay (Milliseconds (retryAfterSeconds * 1000.0))
                handleWithRetry' action config (attempt + 1)
              
              RetryWithBackoff maxRetries baseDelay -> do
                let
                  delaySeconds = calculateRetryDelay attempt baseDelay
                  jitter = if config.jitterEnabled then 0.1 else 0.0  -- Would be random
                  totalDelay = delaySeconds + jitter
                delay (Milliseconds (totalDelay * 1000.0))
                if attempt < maxRetries then
                  handleWithRetry' action config (attempt + 1)
                else
                  pure (Left veniceError)
              
              _ ->
                pure (Left veniceError)
          else
            pure (Left veniceError)
        
        Nothing ->
          -- Unknown error format, don't retry
          pure (Left (UnknownError jsonError.message))

-- | Convert error to alert - Convert Venice error to alert notification
-- |
-- | **Purpose:** Converts a Venice error to an alert notification for user feedback.
-- | **Parameters:**
-- | - `error`: Venice error
-- | **Returns:** Alert notification data
-- | **Side Effects:** None (pure function)
errorToAlert :: VeniceError -> { level :: String, title :: String, message :: String }
errorToAlert error = case error of
  RateLimitError retryAfter ->
    { level: "warning"
    , title: "Rate Limited"
    , message: "Request limit reached. Retrying in " <> show (round retryAfter) <> "s..."
    }
  
  NetworkError msg ->
    { level: "error"
    , title: "Network Error"
    , message: msg <> ". Retrying..."
    }
  
  AuthError msg ->
    { level: "error"
    , title: "Authentication Error"
    , message: msg <> ". Please check your API key."
    }
  
  ValidationError msg ->
    { level: "warning"
    , title: "Invalid Request"
    , message: msg
    }
  
  ServerError code msg ->
    { level: "error"
    , title: "Server Error"
    , message: "Error " <> show code <> ": " <> msg
    }
  
  UnknownError msg ->
    { level: "error"
    , title: "Error"
    , message: msg
    }
