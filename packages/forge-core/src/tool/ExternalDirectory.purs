-- | ExternalDirectory.purs - External directory access tool
-- | TODO: Implement - mirrors forge/src/tool/external-directory.ts
module Tool.ExternalDirectory where

import Prelude
import Effect.Aff (Aff)

type Params = { path :: String }
type Result = { allowed :: Boolean }

assertExternalDirectory :: String -> Aff Unit
assertExternalDirectory _ = notImplemented "Tool.ExternalDirectory.assertExternalDirectory"

notImplemented :: forall a. String -> a
notImplemented = unsafeCrashWith
