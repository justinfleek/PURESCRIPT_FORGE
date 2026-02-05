-- | Timeout utilities
module Opencode.Util.Timeout where

import Prelude
import Effect.Aff (Aff, delay as affDelay, race)
import Effect.Aff as Aff
import Data.Either (Either(..))
import Data.Int as Int

-- | Run with timeout
withTimeout :: forall a. Int -> Aff a -> Aff (Either String a)
withTimeout ms action = do
  timeoutAction <- affDelay (Int.toNumber ms)
  result <- race action (timeoutError ms)
  pure $ case result of
    Left a -> Right a
    Right err -> Left err
  where
    timeoutError :: Int -> Aff String
    timeoutError timeoutMs = do
      affDelay (Int.toNumber timeoutMs)
      pure $ "Operation timed out after " <> show timeoutMs <> "ms"

-- | Delay execution
delay :: Int -> Aff Unit
delay ms = affDelay (Int.toNumber ms)

-- | Create a timeout error message
timeoutError :: String
timeoutError = "Operation timed out"
