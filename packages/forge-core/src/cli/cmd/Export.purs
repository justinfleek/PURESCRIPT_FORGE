-- | Export command
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/export.ts
module Forge.CLI.Cmd.Export where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

type ExportArgs =
  { sessionId :: Maybe String
  , format :: String
  , output :: Maybe String
  }

-- | Execute the export command
execute :: ExportArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Export.execute"
