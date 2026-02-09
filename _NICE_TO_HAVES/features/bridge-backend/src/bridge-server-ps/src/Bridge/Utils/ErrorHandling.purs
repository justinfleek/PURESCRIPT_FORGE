-- | Error Handling Utilities
-- | Common error handling patterns
module Bridge.Utils.ErrorHandling where

import Prelude
import Effect (Effect)
import Effect.Exception (Error, catchException, throwException)
import Data.Either (Either(..))

-- | Safe effect execution with error handling
safeExecute :: forall a. Effect a -> Effect (Either String a)
safeExecute action = do
  catchException handleError (Right <$> action)
  where
    handleError :: Error -> Effect (Either String a)
    handleError err = pure (Left (message err))

-- | Retry effect with exponential backoff
retryWithBackoff :: forall a. Int -> Int -> Effect a -> Effect (Either String a)
retryWithBackoff maxRetries initialDelay action = 
  retryLoop 0 initialDelay
  where
    retryLoop :: Int -> Int -> Effect (Either String a)
    retryLoop currentRetry currentDelay = do
      result <- safeExecute action
      case result of
        Right value -> pure (Right value)
        Left err -> 
          if currentRetry >= maxRetries then
            pure (Left err)
          else do
            delay currentDelay
            retryLoop (currentRetry + 1) (currentDelay * 2)
    
    delay :: Int -> Effect Unit
    delay ms = delayImpl ms

foreign import message :: Error -> String
foreign import delayImpl :: Int -> Effect Unit
