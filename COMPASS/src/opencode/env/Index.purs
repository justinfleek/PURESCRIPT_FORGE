-- | Environment module
module Opencode.Env.Index where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe)
import Bridge.FFI.Node.Process (getEnv)

-- | Get an environment variable
get :: String -> Effect (Maybe String)
get key = getEnv key

-- | Set an environment variable
set :: String -> String -> Effect Unit
set key value = setEnv key value
  where
    foreign import setEnv :: String -> String -> Effect Unit

-- | Check if running in development mode
isDev :: Effect Boolean
isDev = do
  nodeEnv <- getEnv "NODE_ENV"
  pure $ case nodeEnv of
    Just "development" -> true
    Just "dev" -> true
    _ -> false

-- | Check if running in production mode
isProd :: Effect Boolean
isProd = do
  nodeEnv <- getEnv "NODE_ENV"
  pure $ case nodeEnv of
    Just "production" -> true
    Just "prod" -> true
    _ -> false
