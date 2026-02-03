-- | Models command
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/models.ts
module Forge.CLI.Cmd.Models where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

type ModelsArgs =
  { list :: Boolean
  , provider :: Maybe String
  , info :: Maybe String
  }

-- | Execute the models command
execute :: ModelsArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Models.execute"

-- | List available models
listModels :: Maybe String -> Aff (Either String (Array String))
listModels provider = notImplemented "CLI.Cmd.Models.listModels"
