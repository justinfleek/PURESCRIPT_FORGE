-- | Debug Snapshot command
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/debug/snapshot.ts
module Opencode.CLI.Cmd.Debug.Snapshot where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Execute debug snapshot command
execute :: Aff (Either String Unit)
execute = notImplemented "CLI.Cmd.Debug.Snapshot.execute"
