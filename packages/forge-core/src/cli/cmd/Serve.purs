-- | Serve command - start the forge server
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/serve.ts
module Forge.CLI.Cmd.Serve where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

type ServeArgs =
  { port :: Maybe Int
  , host :: Maybe String
  , cors :: Boolean
  }

-- | Execute the serve command
execute :: ServeArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Serve.execute"
