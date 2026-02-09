-- | Export command
module Forge.CLI.Cmd.Export where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe(..))

type ExportArgs =
  { sessionId :: Maybe String
  , format :: String
  , output :: Maybe String
  }

foreign import exportSessionFFI :: String -> String -> String -> Aff (Either String Unit)

-- | Execute the export command
execute :: ExportArgs -> Aff (Either String Unit)
execute args = do
  let sid = case args.sessionId of
        Just s -> s
        Nothing -> ""
  let out = case args.output of
        Just o -> o
        Nothing -> ""
  exportSessionFFI sid args.format out
