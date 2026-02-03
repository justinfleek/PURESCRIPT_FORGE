-- | File route
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/server/routes/file.ts
module Forge.Server.Routes.File where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Read a file
read :: String -> Aff (Either String String)
read path = notImplemented "Server.Routes.File.read"

-- | Write a file
write :: String -> String -> Aff (Either String Unit)
write path content = notImplemented "Server.Routes.File.write"

-- | List directory
list :: String -> Aff (Either String (Array String))
list path = notImplemented "Server.Routes.File.list"
