-- | Retry Logic - Exponential Backoff Retry Mechanism
-- |
-- | **What:** Implements retry logic with exponential backoff for retryable operations.
-- |         Provides configurable retry strategies and backoff calculation.
-- | **Why:** Handles transient failures gracefully. Prevents overwhelming services
-- |         with rapid retries. Improves reliability for network and external service calls.
-- | **How:** Retries operations with exponentially increasing delays between attempts.
-- |         Stops after max retries or on terminal errors.
-- |
-- | **Dependencies:**
-- | - `Bridge.Error.Taxonomy`: Error classification
-- | - `Effect.Aff`: Async effects
-- | - `Bridge.FFI.Node.Pino`: Structured logging
-- |
-- | **Mathematical Foundation:**
-- | - **Backoff Formula:** `delay = baseDelay * (2 ^ attemptNumber)`
-- | - **Max Delay:** `min(delay, maxDelay)`
-- | - **Jitter:** `delay = delay + random(0, jitter)` (prevents thundering herd)
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Bridge.Error.Retry as Retry
-- |
-- | -- Retry operation
-- | result <- Retry.withRetry {
-- |   maxRetries: 3
-- |   , baseDelay: 1000
-- |   , maxDelay: 10000
-- |   , jitter: 500
-- | } \attempt -> do
-- |   -- Operation that may fail
-- |   callVeniceAPI
-- | ```
module Bridge.Error.Retry where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, delay, Milliseconds(..))
import Effect.Class (liftEffect)
import Effect.Random (random)
import Data.Either (Either(..))
import Data.Int (toNumber)
import Bridge.Error.Taxonomy (BridgeError, isRetryable)
import Bridge.FFI.Node.Pino (Logger, info)
import Bridge.FFI.Node.Pino as Pino

-- | FFI: Random range
foreign import randomRange :: Int -> Int -> Effect Int

-- | Retry configuration
type RetryConfig =
  { maxRetries :: Int
  , baseDelay :: Int -- Milliseconds
  , maxDelay :: Int -- Milliseconds
  , jitter :: Int -- Milliseconds
  }

-- | Default retry configuration
defaultRetryConfig :: RetryConfig
defaultRetryConfig =
  { maxRetries: 3
  , baseDelay: 1000
  , maxDelay: 10000
  , jitter: 500
  }

-- | Retry attempt result
type RetryAttempt a =
  { attempt :: Int
  , result :: Either BridgeError a
  , delay :: Int
  }

-- | Calculate backoff delay
-- |
-- | **Purpose:** Computes delay for next retry attempt using exponential backoff.
-- | **Parameters:**
-- | - `attempt`: Attempt number (0-indexed)
-- | - `config`: Retry configuration
-- | **Returns:** Delay in milliseconds
calculateBackoff :: Int -> RetryConfig -> Aff Int
calculateBackoff attempt config = do
  let baseDelay = config.baseDelay * (pow 2 attempt)
  let cappedDelay = min baseDelay config.maxDelay
  jitterAmount <- liftEffect $ randomRange 0 config.jitter
  pure (cappedDelay + jitterAmount)
  where
    pow :: Int -> Int -> Int
    pow base exp = if exp <= 0 then 1 else base * pow base (exp - 1)

-- | Retry operation with exponential backoff
-- |
-- | **Purpose:** Retries an operation with exponential backoff until success or max retries.
-- | **Parameters:**
-- | - `config`: Retry configuration
-- | - `operation`: Operation to retry (returns Either BridgeError a)
-- | - `logger`: Logger for retry attempts
-- | **Returns:** Either error or result
-- |
-- | **Logic:**
-- | - Attempt operation
-- | - If success, return result
-- | - If error and retryable and attempts < maxRetries, wait and retry
-- | - If error and not retryable or attempts >= maxRetries, return error
withRetry :: forall a. RetryConfig -> (Int -> Aff (Either BridgeError a)) -> Logger -> Aff (Either BridgeError a)
withRetry config operation logger = do
  retryLoop 0
  where
    retryLoop :: Int -> Aff (Either BridgeError a)
    retryLoop attempt = do
      result <- operation attempt
      case result of
        Right value -> pure (Right value)
        Left error -> do
          if isRetryable error && attempt < config.maxRetries then
            do
              delayMs <- calculateBackoff attempt config
              liftEffect $ Pino.info logger ("Retrying after " <> show delayMs <> "ms (attempt " <> show (attempt + 1) <> "/" <> show config.maxRetries <> ")")
              delay (Milliseconds (toNumber delayMs))
              retryLoop (attempt + 1)
          else
            pure (Left error)

-- | Retry with custom backoff function
-- |
-- | **Purpose:** Retries operation with custom backoff calculation.
-- | **Parameters:**
-- | - `config`: Retry configuration
-- | - `backoffFn`: Custom backoff function (attempt -> delay)
-- | - `operation`: Operation to retry
-- | - `logger`: Logger
-- | **Returns:** Either error or result
withCustomRetry :: forall a. RetryConfig -> (Int -> Aff Int) -> (Int -> Aff (Either BridgeError a)) -> Logger -> Aff (Either BridgeError a)
withCustomRetry config backoffFn operation logger = do
  retryLoop 0
  where
    retryLoop :: Int -> Aff (Either BridgeError a)
    retryLoop attempt = do
      result <- operation attempt
      case result of
        Right value -> pure (Right value)
        Left error -> do
          if isRetryable error && attempt < config.maxRetries then
            do
              delayMs <- backoffFn attempt
              liftEffect $ Pino.info logger ("Retrying after " <> show delayMs <> "ms")
              delay (Milliseconds (toNumber delayMs))
              retryLoop (attempt + 1)
          else
            pure (Left error)
