-- | Serve command - start the opencode server
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/serve.ts
module Opencode.CLI.Cmd.Serve where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

type ServeArgs =
  { port :: Maybe Int
  , host :: Maybe String
  , cors :: Boolean
  }

-- | Execute the serve command
execute :: ServeArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Serve.execute"
