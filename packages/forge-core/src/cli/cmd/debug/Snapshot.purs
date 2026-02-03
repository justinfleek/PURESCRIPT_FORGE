-- | Debug Snapshot command
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/debug/snapshot.ts
module Forge.CLI.Cmd.Debug.Snapshot where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Execute debug snapshot command
execute :: Aff (Either String Unit)
execute = notImplemented "CLI.Cmd.Debug.Snapshot.execute"
