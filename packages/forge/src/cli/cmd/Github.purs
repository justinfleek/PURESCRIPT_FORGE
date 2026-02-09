-- | GitHub integration command
module Forge.CLI.Cmd.Github where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe(..))

type GithubArgs =
  { action :: String
  , repo :: Maybe String
  , issue :: Maybe Int
  , pr :: Maybe Int
  }

foreign import githubExecuteFFI :: String -> String -> Aff (Either String Unit)

-- | Execute the github command
execute :: GithubArgs -> Aff (Either String Unit)
execute args = do
  let repo = case args.repo of
        Just r -> r
        Nothing -> ""
  githubExecuteFFI args.action repo
