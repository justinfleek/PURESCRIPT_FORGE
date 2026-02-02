-- | Web command
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/web.ts
module Opencode.CLI.Cmd.Web where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

type WebArgs =
  { open :: Boolean
  , url :: Maybe String
  }

-- | Execute the web command
execute :: WebArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Web.execute"
