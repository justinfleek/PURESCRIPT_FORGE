-- | Import command
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/import.ts
module Opencode.CLI.Cmd.Import where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

type ImportArgs =
  { source :: String
  , format :: Maybe String
  }

-- | Execute the import command
execute :: ImportArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Import.execute"
