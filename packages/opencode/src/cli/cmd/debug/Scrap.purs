-- | Debug Scrap command
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/debug/scrap.ts
module Opencode.CLI.Cmd.Debug.Scrap where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Execute debug scrap command
execute :: Aff (Either String Unit)
execute = notImplemented "CLI.Cmd.Debug.Scrap.execute"
