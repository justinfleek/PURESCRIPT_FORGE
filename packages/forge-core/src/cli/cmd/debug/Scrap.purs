-- | Debug Scrap command
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/debug/scrap.ts
module Forge.CLI.Cmd.Debug.Scrap where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Execute debug scrap command
execute :: Aff (Either String Unit)
execute = notImplemented "CLI.Cmd.Debug.Scrap.execute"
