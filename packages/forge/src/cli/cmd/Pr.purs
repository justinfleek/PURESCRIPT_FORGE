-- | PR (Pull Request) command
module Forge.CLI.Cmd.Pr where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe(..))

type PrArgs =
  { action :: String
  , number :: Maybe Int
  , title :: Maybe String
  , body :: Maybe String
  }

foreign import prExecuteFFI :: String -> Int -> String -> String -> Aff (Either String Unit)

-- | Execute the pr command
execute :: PrArgs -> Aff (Either String Unit)
execute args = do
  let num = case args.number of
        Just n -> n
        Nothing -> 0
  let ttl = case args.title of
        Just t -> t
        Nothing -> ""
  let bod = case args.body of
        Just b -> b
        Nothing -> ""
  prExecuteFFI args.action num ttl bod
