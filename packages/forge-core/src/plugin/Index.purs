-- | Plugin Index
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/plugin/index.ts
module Forge.Plugin.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Plugin info
type Plugin =
  { name :: String
  , version :: String
  , enabled :: Boolean
  }

-- | List plugins
list :: Aff (Either String (Array Plugin))
list = notImplemented "Plugin.Index.list"

-- | Enable a plugin
enable :: String -> Aff (Either String Unit)
enable name = notImplemented "Plugin.Index.enable"

-- | Disable a plugin
disable :: String -> Aff (Either String Unit)
disable name = notImplemented "Plugin.Index.disable"
