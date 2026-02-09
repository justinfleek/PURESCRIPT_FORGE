-- | Serve command - start the forge server
module Forge.CLI.Cmd.Serve where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe(..))

type ServeArgs =
  { port :: Maybe Int
  , host :: Maybe String
  , cors :: Boolean
  }

foreign import startServerFFI :: Int -> String -> Boolean -> Aff (Either String Unit)

-- | Execute the serve command
execute :: ServeArgs -> Aff (Either String Unit)
execute args = do
  let port = case args.port of
        Just p -> p
        Nothing -> 8765
  let host = case args.host of
        Just h -> h
        Nothing -> "0.0.0.0"
  startServerFFI port host args.cors
