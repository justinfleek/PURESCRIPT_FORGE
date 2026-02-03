-- | GitHub integration command
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/github.ts
module Forge.CLI.Cmd.Github where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

type GithubArgs =
  { action :: String
  , repo :: Maybe String
  , issue :: Maybe Int
  , pr :: Maybe Int
  }

-- | Execute the github command
execute :: GithubArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Github.execute"
