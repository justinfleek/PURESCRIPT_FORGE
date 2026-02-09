-- | Models command
module Forge.CLI.Cmd.Models where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)

type ModelsArgs =
  { list :: Boolean
  , provider :: Maybe String
  , info :: Maybe String
  }

-- | Execute the models command
execute :: ModelsArgs -> Aff (Either String Unit)
execute args = executeFFI args

-- | List available models
listModels :: Maybe String -> Aff (Either String (Array String))
listModels provider = listModelsFFI provider

foreign import executeFFI :: ModelsArgs -> Aff (Either String Unit)
foreign import listModelsFFI :: Maybe String -> Aff (Either String (Array String))
