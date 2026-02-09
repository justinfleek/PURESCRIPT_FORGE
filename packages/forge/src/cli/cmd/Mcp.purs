-- | MCP (Model Context Protocol) command
module Forge.CLI.Cmd.Mcp where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe(..))

type McpArgs =
  { list :: Boolean
  , add :: Maybe String
  , remove :: Maybe String
  , info :: Maybe String
  }

foreign import mcpExecuteFFI :: Boolean -> String -> String -> String -> Aff (Either String Unit)

-- | Execute the mcp command
execute :: McpArgs -> Aff (Either String Unit)
execute args = do
  let addName = case args.add of
        Just a -> a
        Nothing -> ""
  let removeName = case args.remove of
        Just r -> r
        Nothing -> ""
  let infoName = case args.info of
        Just i -> i
        Nothing -> ""
  mcpExecuteFFI args.list addName removeName infoName
