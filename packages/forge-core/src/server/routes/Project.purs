-- | Project route
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/server/routes/project.ts
module Forge.Server.Routes.Project where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Get project info
get :: Aff (Either String String)
get = notImplemented "Server.Routes.Project.get"

-- | List project files
listFiles :: Aff (Either String (Array String))
listFiles = notImplemented "Server.Routes.Project.listFiles"
