-- | Uninstall command
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/uninstall.ts
module Opencode.CLI.Cmd.Uninstall where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

type UninstallArgs =
  { force :: Boolean
  , keepData :: Boolean
  }

-- | Execute the uninstall command
execute :: UninstallArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Uninstall.execute"
