-- | CLI Bootstrap
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/bootstrap.ts
module Opencode.CLI.Bootstrap where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Project.Instance (Instance)
import Opencode.Project.Bootstrap (InstanceBootstrap)
import Opencode.Util.NotImplemented (notImplemented)

-- | Bootstrap the CLI with a working directory and callback
bootstrap :: forall a. String -> Aff a -> Aff (Either String a)
bootstrap directory callback = notImplemented "CLI.Bootstrap.bootstrap"
