-- | Stats command
module Forge.CLI.Cmd.Stats where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe(..))

type StatsArgs =
  { period :: Maybe String
  , format :: Maybe String
  }

foreign import statsFFI :: String -> String -> Aff (Either String Unit)

-- | Execute the stats command
execute :: StatsArgs -> Aff (Either String Unit)
execute args = do
  let period = case args.period of
        Just p -> p
        Nothing -> "all"
  let fmt = case args.format of
        Just f -> f
        Nothing -> "table"
  statsFFI period fmt
