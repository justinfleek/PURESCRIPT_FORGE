-- | Permission route
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/server/routes/permission.ts
module Forge.Server.Routes.Permission where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Permission response type
data PermissionResponse = Allow | Deny | AllowAlways

-- | Respond to a permission request
respond :: String -> String -> PermissionResponse -> Aff (Either String Unit)
respond sessionId permissionId response = notImplemented "Server.Routes.Permission.respond"
