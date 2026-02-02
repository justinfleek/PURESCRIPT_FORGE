-- | Permission route
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/server/routes/permission.ts
module Opencode.Server.Routes.Permission where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Permission response type
data PermissionResponse = Allow | Deny | AllowAlways

-- | Respond to a permission request
respond :: String -> String -> PermissionResponse -> Aff (Either String Unit)
respond sessionId permissionId response = notImplemented "Server.Routes.Permission.respond"
