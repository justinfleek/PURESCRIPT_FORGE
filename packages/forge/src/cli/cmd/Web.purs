-- | Web command
module Forge.CLI.Cmd.Web where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))

type WebArgs =
  { open :: Boolean
  , url :: Maybe String
  }

foreign import openBrowserFFI :: String -> Aff (Either String Unit)

-- | Execute the web command
execute :: WebArgs -> Aff (Either String Unit)
execute args = do
  let url = case args.url of
        Just u -> u
        Nothing -> "http://localhost:8765"
  if args.open
    then openBrowserFFI url
    else pure $ Right unit
