-- | MCP (Model Context Protocol) command
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/cli/cmd/mcp.ts
module Forge.CLI.Cmd.Mcp where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

type McpArgs =
  { list :: Boolean
  , add :: Maybe String
  , remove :: Maybe String
  , info :: Maybe String
  }

-- | Execute the mcp command
execute :: McpArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Mcp.execute"
