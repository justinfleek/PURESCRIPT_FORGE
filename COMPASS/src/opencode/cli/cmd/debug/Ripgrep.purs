-- | Debug Ripgrep command
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/debug/ripgrep.ts
module Opencode.CLI.Cmd.Debug.Ripgrep where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Execute debug ripgrep command
execute :: String -> Aff (Either String Unit)
execute pattern = notImplemented "CLI.Cmd.Debug.Ripgrep.execute"
