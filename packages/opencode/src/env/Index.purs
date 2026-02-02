-- | Environment module
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/env/index.ts
module Opencode.Env.Index where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Get an environment variable
get :: String -> Effect (Maybe String)
get key = notImplemented "Env.Index.get"

-- | Set an environment variable
set :: String -> String -> Effect Unit
set key value = notImplemented "Env.Index.set"

-- | Check if running in development mode
isDev :: Effect Boolean
isDev = notImplemented "Env.Index.isDev"

-- | Check if running in production mode
isProd :: Effect Boolean
isProd = notImplemented "Env.Index.isProd"
