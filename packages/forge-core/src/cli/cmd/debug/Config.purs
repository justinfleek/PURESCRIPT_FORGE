-- | Debug Config command
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/debug/config.ts
module Forge.CLI.Cmd.Debug.Config where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Execute debug config command
execute :: Aff (Either String Unit)
execute = notImplemented "CLI.Cmd.Debug.Config.execute"
