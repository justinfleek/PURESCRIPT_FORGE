-- | Upgrade command
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/upgrade.ts
module Opencode.CLI.Cmd.Upgrade where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

type UpgradeArgs =
  { version :: Maybe String
  , force :: Boolean
  , check :: Boolean
  }

-- | Execute the upgrade command
execute :: UpgradeArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Upgrade.execute"
