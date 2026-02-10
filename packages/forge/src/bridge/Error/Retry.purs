-- | Error Retry - Exponential backoff retry logic
module Bridge.Error.Retry where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, delay)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Int (toNumber)
import Data.Time.Duration (Milliseconds(..))
import Bridge.Error.Taxonomy (BridgeError, isRetryable)
import Bridge.FFI.Node.Pino as Pino

-- | Retry configuration
type RetryConfig =
  { maxRetries :: Int
  , baseDelay :: Int
  , maxDelay :: Int
  , jitter :: Int
  }

-- | Retry attempt result
type RetryAttempt a =
  { attempt :: Int
  , result :: Either BridgeError a
  , delay :: Int
  }

-- | Default retry configuration
defaultRetryConfig :: RetryConfig
defaultRetryConfig =
  { maxRetries: 3
  , baseDelay: 1000
  , maxDelay: 10000
  , jitter: 500
  }

-- | FFI for random number in range
foreign import randomRangeImpl :: Int -> Int -> EffectFnAff Int

-- | Calculate exponential backoff delay
calculateBackoff :: Int -> RetryConfig -> Aff Int
calculateBackoff attempt config = do
  let base = config.baseDelay * pow 2 attempt
  let capped = min base config.maxDelay
  jitterVal <- fromEffectFnAff $ randomRangeImpl 0 config.jitter
  pure (capped + jitterVal)
  where
    pow :: Int -> Int -> Int
    pow _ 0 = 1
    pow b n = b * pow b (n - 1)

-- | Retry an operation with exponential backoff
withRetry :: forall a. RetryConfig -> (Int -> Aff (Either BridgeError a)) -> Pino.Logger -> Aff (Either BridgeError a)
withRetry config operation logger = go 0
  where
    go :: Int -> Aff (Either BridgeError a)
    go attempt = do
      result <- operation attempt
      case result of
        Right val -> pure (Right val)
        Left err ->
          if isRetryable err && attempt < config.maxRetries then do
            backoff <- calculateBackoff attempt config
            liftEffect $ Pino.warn logger ("Retrying (attempt " <> show (attempt + 1) <> "/" <> show config.maxRetries <> ") after " <> show backoff <> "ms")
            delay (Milliseconds (toNumber backoff))
            go (attempt + 1)
          else
            pure (Left err)

-- | Retry with custom backoff function
withCustomRetry :: forall a. RetryConfig -> (Int -> Aff Int) -> (Int -> Aff (Either BridgeError a)) -> Pino.Logger -> Aff (Either BridgeError a)
withCustomRetry config backoffFn operation logger = go 0
  where
    go :: Int -> Aff (Either BridgeError a)
    go attempt = do
      result <- operation attempt
      case result of
        Right val -> pure (Right val)
        Left err ->
          if isRetryable err && attempt < config.maxRetries then do
            backoff <- backoffFn attempt
            liftEffect $ Pino.warn logger ("Custom retry (attempt " <> show (attempt + 1) <> ") after " <> show backoff <> "ms")
            delay (Milliseconds (toNumber backoff))
            go (attempt + 1)
          else
            pure (Left err)
