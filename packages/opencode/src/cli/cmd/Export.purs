-- | Export command
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/export.ts
module Opencode.CLI.Cmd.Export where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

type ExportArgs =
  { sessionId :: Maybe String
  , format :: String
  , output :: Maybe String
  }

-- | Execute the export command
execute :: ExportArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Export.execute"
