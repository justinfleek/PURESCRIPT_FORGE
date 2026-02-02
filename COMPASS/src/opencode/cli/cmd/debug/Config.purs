-- | Debug Config command
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/debug/config.ts
module Opencode.CLI.Cmd.Debug.Config where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Execute debug config command
execute :: Aff (Either String Unit)
execute = notImplemented "CLI.Cmd.Debug.Config.execute"
