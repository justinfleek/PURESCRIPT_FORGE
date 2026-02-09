-- | Permission route
-- | 1:1 parity with opencode-dev/packages/opencode/src/server/routes/permission.ts
module Forge.Server.Routes.Permission where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Foreign (Foreign)

-- | Permission response type
data PermissionResponse = Allow | Deny | AllowAlways

-- | Respond to a permission request
respond :: String -> String -> String -> Aff (Either String Unit)
respond sessionID requestID response = respondFFI sessionID requestID response

-- | List pending permission requests
pending :: String -> Aff (Either String (Array Foreign))
pending sessionID = pendingFFI sessionID

-- | Get permission rules
rules :: String -> Aff (Either String (Array Foreign))
rules sessionID = rulesFFI sessionID

foreign import respondFFI :: String -> String -> String -> Aff (Either String Unit)
foreign import pendingFFI :: String -> Aff (Either String (Array Foreign))
foreign import rulesFFI :: String -> Aff (Either String (Array Foreign))
