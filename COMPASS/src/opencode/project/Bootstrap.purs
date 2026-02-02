-- | Project Bootstrap
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/project/bootstrap.ts
module Opencode.Project.Bootstrap where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Bootstrap a project instance
bootstrap :: String -> Aff (Either String Unit)
bootstrap directory = notImplemented "Project.Bootstrap.bootstrap"

-- | Instance bootstrap function type
type InstanceBootstrap = Unit
