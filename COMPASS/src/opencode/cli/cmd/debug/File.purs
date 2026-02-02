-- | Debug File command
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/debug/file.ts
module Opencode.CLI.Cmd.Debug.File where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Execute debug file command
execute :: String -> Aff (Either String Unit)
execute path = notImplemented "CLI.Cmd.Debug.File.execute"
