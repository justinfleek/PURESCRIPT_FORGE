-- | Import command
module Forge.CLI.Cmd.Import where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe)

type ImportArgs =
  { source :: String
  , format :: Maybe String
  }

foreign import importSessionFFI :: String -> Aff (Either String Unit)

-- | Execute the import command
execute :: ImportArgs -> Aff (Either String Unit)
execute args = importSessionFFI args.source
