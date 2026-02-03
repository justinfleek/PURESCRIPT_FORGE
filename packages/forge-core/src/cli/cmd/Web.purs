-- | Web command
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/web.ts
module Forge.CLI.Cmd.Web where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

type WebArgs =
  { open :: Boolean
  , url :: Maybe String
  }

-- | Execute the web command
execute :: WebArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Web.execute"
