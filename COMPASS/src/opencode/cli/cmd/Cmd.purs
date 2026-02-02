-- | CLI Command module
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/cmd.ts
module Opencode.CLI.Cmd.Cmd where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Command definition type
type CommandDef a =
  { command :: String
  , describe :: String
  , handler :: a -> Aff (Either String Unit)
  }

-- | Create a command definition
cmd :: forall a. CommandDef a -> CommandDef a
cmd input = input
