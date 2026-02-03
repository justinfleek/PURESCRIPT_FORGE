-- | Logging utilities
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/util/log.ts
module Forge.Util.Log where

import Prelude
import Effect (Effect)
import Forge.Util.NotImplemented (notImplemented)

-- | Logger configuration
type LoggerConfig =
  { service :: String
  , level :: String
  }

-- | Logger instance
type Logger =
  { debug :: String -> Effect Unit
  , info :: String -> Effect Unit
  , warn :: String -> Effect Unit
  , error :: String -> Effect Unit
  }

-- | Create a logger
create :: LoggerConfig -> Logger
create config =
  { debug: \_ -> notImplemented "Util.Log.debug"
  , info: \_ -> notImplemented "Util.Log.info"
  , warn: \_ -> notImplemented "Util.Log.warn"
  , error: \_ -> notImplemented "Util.Log.error"
  }
