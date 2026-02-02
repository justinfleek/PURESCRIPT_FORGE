-- | MCP (Model Context Protocol) command
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/cli/cmd/mcp.ts
module Opencode.CLI.Cmd.Mcp where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

type McpArgs =
  { list :: Boolean
  , add :: Maybe String
  , remove :: Maybe String
  , info :: Maybe String
  }

-- | Execute the mcp command
execute :: McpArgs -> Aff (Either String Unit)
execute args = notImplemented "CLI.Cmd.Mcp.execute"
