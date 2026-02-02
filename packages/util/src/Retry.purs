-- | Retry with exponential backoff
-- | Migrated from opencode-dev/packages/util/src/retry.ts
module Opencode.Util.Retry
  ( RetryOptions
  , defaultOptions
  , retry
  ) where

import Prelude
import Effect.Aff (Aff, delay, try)
import Effect.Aff.Class (liftAff)
import Data.Time.Duration (Milliseconds(..))
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (toLower, contains, Pattern(..))
import Data.Array (any)
import Control.Monad.Error.Class (throwError)
import Effect.Exception (Error, message)
import Data.Number (pow)

type RetryOptions =
  { attempts :: Maybe Int
  , delay :: Maybe Number
  , factor :: Maybe Number
  , maxDelay :: Maybe Number
  , retryIf :: Maybe (Error -> Boolean)
  }

defaultOptions :: RetryOptions
defaultOptions =
  { attempts: Nothing
  , delay: Nothing
  , factor: Nothing
  , maxDelay: Nothing
  , retryIf: Nothing
  }

-- | Retry an Aff action with exponential backoff
retry :: forall a. (Unit -> Aff a) -> RetryOptions -> Aff a
retry fn opts = go 0 Nothing
  where
  attempts = fromMaybe 3 opts.attempts
  baseDelay = fromMaybe 500.0 opts.delay
  factor = fromMaybe 2.0 opts.factor
  maxDelay = fromMaybe 10000.0 opts.maxDelay
  retryIf = fromMaybe isTransientError opts.retryIf

  go :: Int -> Maybe Error -> Aff a
  go attempt lastErr
    | attempt >= attempts = case lastErr of
        Just e -> throwError e
        Nothing -> fn unit
    | otherwise = do
        result <- try (fn unit)
        case result of
          Right value -> pure value
          Left err ->
            if attempt == attempts - 1 || not (retryIf err)
              then throwError err
              else do
                let wait = min (baseDelay * pow factor (toNumber attempt)) maxDelay
                delay (Milliseconds wait)
                go (attempt + 1) (Just err)

-- Check for transient network errors
isTransientError :: Error -> Boolean
isTransientError err =
  let msg = toLower (message err)
  in any (\p -> contains (Pattern p) msg) transientMessages

transientMessages :: Array String
transientMessages =
  [ "load failed"
  , "network connection was lost"
  , "network request failed"
  , "failed to fetch"
  , "econnreset"
  , "econnrefused"
  , "etimedout"
  , "socket hang up"
  ]

foreign import toNumber :: Int -> Number
