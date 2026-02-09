{-|
Module      : Forge.Session.Retry
Description : Session Retry Logic

Handles retry logic for failed operations including message sending,
tool execution, and API calls.

== Retry Strategy

Uses exponential backoff with jitter:
- Initial delay: 1 second
- Exponential multiplier: 2x
- Max delay: 30 seconds
- Max attempts: 3 (configurable)
-}
module Forge.Session.Retry
  ( -- * Types
    RetryConfig
  , RetryResult(..)
  , RetryableError(..)
    -- * Retry Operations
  , retryMessage
  , retryFrom
  , retryWithConfig
    -- * Utilities
  , isRetryable
  , calculateBackoff
    -- * Default Config
  , defaultRetryConfig
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff, delay)
import Data.Time.Duration (Milliseconds(..))

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Retry configuration
type RetryConfig =
  { maxAttempts :: Int
  , initialDelayMs :: Int
  , maxDelayMs :: Int
  , multiplier :: Number
  , jitterFactor :: Number
  }

-- | Retry result
data RetryResult
  = RetrySuccess
  | RetryFailed String
  | RetryExhausted Int  -- Number of attempts made

derive instance eqRetryResult :: Eq RetryResult

instance showRetryResult :: Show RetryResult where
  show RetrySuccess = "success"
  show (RetryFailed err) = "failed: " <> err
  show (RetryExhausted n) = "exhausted after " <> show n <> " attempts"

-- | Errors that can be retried
data RetryableError
  = RateLimitError Int     -- Retry after N seconds
  | TimeoutError
  | NetworkError String
  | TemporaryError String
  | PermanentError String  -- Should not be retried

derive instance eqRetryableError :: Eq RetryableError

-- ============================================================================
-- FFI
-- ============================================================================

foreign import getMessageFFI :: String -> String -> Aff (Maybe { content :: String, role :: String })
foreign import resendMessageFFI :: String -> String -> Aff (Either String Unit)
foreign import getMessagesFromFFI :: String -> String -> Aff (Array { id :: String, content :: String, role :: String })
foreign import randomFFI :: Aff Number

-- ============================================================================
-- DEFAULT CONFIG
-- ============================================================================

-- | Default retry configuration
defaultRetryConfig :: RetryConfig
defaultRetryConfig =
  { maxAttempts: 3
  , initialDelayMs: 1000
  , maxDelayMs: 30000
  , multiplier: 2.0
  , jitterFactor: 0.1
  }

-- ============================================================================
-- RETRY OPERATIONS
-- ============================================================================

{-| Retry a failed message.

Attempts to resend a specific message that previously failed.
-}
retryMessage :: String -> String -> Aff (Either String Unit)
retryMessage sessionId messageId = 
  retryWithConfig sessionId messageId defaultRetryConfig

{-| Retry from a specific message.

Replays all messages from the given point forward.
-}
retryFrom :: String -> String -> Aff (Either String Unit)
retryFrom sessionId fromMessageId = do
  messages <- getMessagesFromFFI sessionId fromMessageId
  if Array.null messages
    then pure $ Left "No messages to retry"
    else go messages
  where
    go :: Array { id :: String, content :: String, role :: String } -> Aff (Either String Unit)
    go [] = pure $ Right unit
    go msgs = case Array.uncons msgs of
      Nothing -> pure $ Right unit
      Just { head: msg, tail: rest } -> do
        result <- retryMessage sessionId msg.id
        case result of
          Left err -> pure $ Left err
          Right _ -> go rest

{-| Retry with custom configuration. -}
retryWithConfig :: String -> String -> RetryConfig -> Aff (Either String Unit)
retryWithConfig sessionId messageId config = go 1
  where
    go :: Int -> Aff (Either String Unit)
    go attempt
      | attempt > config.maxAttempts = pure $ Left ("Max retry attempts (" <> show config.maxAttempts <> ") exceeded")
      | otherwise = do
          result <- resendMessageFFI sessionId messageId
          case result of
            Right _ -> pure $ Right unit
            Left err ->
              if isRetryable (parseError err) && attempt < config.maxAttempts
                then do
                  delayMs <- calculateBackoff config attempt
                  delay (Milliseconds (toNumber delayMs))
                  go (attempt + 1)
                else pure $ Left err

-- ============================================================================
-- UTILITIES
-- ============================================================================

{-| Check if an error is retryable. -}
isRetryable :: RetryableError -> Boolean
isRetryable (RateLimitError _) = true
isRetryable TimeoutError = true
isRetryable (NetworkError _) = true
isRetryable (TemporaryError _) = true
isRetryable (PermanentError _) = false

{-| Calculate backoff delay with jitter.

Uses exponential backoff: delay = min(initialDelay * multiplier^attempt, maxDelay)
Adds random jitter to prevent thundering herd.
-}
calculateBackoff :: RetryConfig -> Int -> Aff Int
calculateBackoff config attempt = do
  jitter <- randomFFI
  let baseDelay = toNumber config.initialDelayMs * pow config.multiplier (toNumber (attempt - 1))
      cappedDelay = min baseDelay (toNumber config.maxDelayMs)
      jitterAmount = cappedDelay * config.jitterFactor * (jitter * 2.0 - 1.0)
  pure $ floor (cappedDelay + jitterAmount)

-- ============================================================================
-- HELPERS
-- ============================================================================

parseError :: String -> RetryableError
parseError err
  | contains "rate limit" err = RateLimitError 60
  | contains "timeout" err = TimeoutError
  | contains "network" err || contains "ECONNREFUSED" err = NetworkError err
  | contains "temporary" err || contains "503" err || contains "502" err = TemporaryError err
  | otherwise = PermanentError err

contains :: String -> String -> Boolean
contains needle haystack = containsImpl needle haystack

foreign import containsImpl :: String -> String -> Boolean

pow :: Number -> Number -> Number
pow = powImpl

foreign import powImpl :: Number -> Number -> Number

toNumber :: Int -> Number
toNumber = toNumberImpl

foreign import toNumberImpl :: Int -> Number

floor :: Number -> Int
floor = floorImpl

foreign import floorImpl :: Number -> Int
