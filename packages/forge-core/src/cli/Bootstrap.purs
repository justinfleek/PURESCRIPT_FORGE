-- | CLI Bootstrap
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/bootstrap.ts
module Forge.CLI.Bootstrap where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Project.Instance (Instance)
import Forge.Project.Bootstrap (InstanceBootstrap)
import Forge.Util.NotImplemented (notImplemented)

-- | Bootstrap the CLI with a working directory and callback
bootstrap :: forall a. String -> Aff a -> Aff (Either String a)
bootstrap directory callback = notImplemented "CLI.Bootstrap.bootstrap"
