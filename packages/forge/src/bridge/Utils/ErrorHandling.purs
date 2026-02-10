-- | Error Handling Utilities
module Bridge.Utils.ErrorHandling where

import Prelude
import Effect (Effect)
import Effect.Exception (try, message)
import Data.Either (Either(..))

-- | FFI for synchronous delay
foreign import delayImpl :: Int -> Effect Unit

-- | Safely execute an Effect, catching exceptions
safeExecute :: forall a. Effect a -> Effect (Either String a)
safeExecute action = do
  result <- try action
  case result of
    Left err -> pure (Left (message err))
    Right val -> pure (Right val)

-- | Retry with exponential backoff (synchronous)
retryWithBackoff :: forall a. Int -> Int -> Effect a -> Effect (Either String a)
retryWithBackoff maxRetries baseDelay action = go 0
  where
    go :: Int -> Effect (Either String a)
    go attempt = do
      result <- safeExecute action
      case result of
        Right val -> pure (Right val)
        Left err ->
          if attempt < maxRetries then do
            let currentDelay = baseDelay * pow 2 attempt
            delayImpl currentDelay
            go (attempt + 1)
          else
            pure (Left err)

    pow :: Int -> Int -> Int
    pow _ 0 = 1
    pow b n = b * pow b (n - 1)
