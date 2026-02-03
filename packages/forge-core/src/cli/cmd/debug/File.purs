-- | Debug File command
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/debug/file.ts
module Forge.CLI.Cmd.Debug.File where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Execute debug file command
execute :: String -> Aff (Either String Unit)
execute path = notImplemented "CLI.Cmd.Debug.File.execute"
