-- | CLI Command module
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/cmd.ts
module Forge.CLI.Cmd.Cmd where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Command definition type
type CommandDef a =
  { command :: String
  , describe :: String
  , handler :: a -> Aff (Either String Unit)
  }

-- | Create a command definition
cmd :: forall a. CommandDef a -> CommandDef a
cmd input = input
