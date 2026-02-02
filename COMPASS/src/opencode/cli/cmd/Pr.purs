-- | PR (Pull Request) command
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/pr.ts
module Opencode.CLI.Cmd.Pr where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

type PrArgs =
  { action :: String  -- create, review, merge, etc.
  , number :: Maybe Int
  , title :: Maybe String
  , body :: Maybe String
  }

-- | Execute the pr command
execute :: PrArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Pr.execute"
