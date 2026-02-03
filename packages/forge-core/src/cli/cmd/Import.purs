-- | Import command
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/import.ts
module Forge.CLI.Cmd.Import where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

type ImportArgs =
  { source :: String
  , format :: Maybe String
  }

-- | Execute the import command
execute :: ImportArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Import.execute"
