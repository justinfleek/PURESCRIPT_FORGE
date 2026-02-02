-- | Generate command
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/generate.ts
module Opencode.CLI.Cmd.Generate where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

type GenerateArgs =
  { template :: String
  , output :: Maybe String
  , force :: Boolean
  }

-- | Execute the generate command
execute :: GenerateArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Generate.execute"
