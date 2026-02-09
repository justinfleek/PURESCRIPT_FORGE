-- | Generate command
module Forge.CLI.Cmd.Generate where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe(..))

type GenerateArgs =
  { template :: String
  , output :: Maybe String
  , force :: Boolean
  }

foreign import generateFFI :: String -> String -> Boolean -> Aff (Either String Unit)

-- | Execute the generate command
execute :: GenerateArgs -> Aff (Either String Unit)
execute args = do
  let outputDir = case args.output of
        Just o -> o
        Nothing -> "."
  generateFFI args.template outputDir args.force
