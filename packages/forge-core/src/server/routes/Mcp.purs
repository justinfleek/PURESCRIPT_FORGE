-- | MCP route
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/server/routes/mcp.ts
module Forge.Server.Routes.Mcp where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | List MCP servers
list :: Aff (Either String (Array String))
list = notImplemented "Server.Routes.Mcp.list"

-- | Call MCP tool
callTool :: String -> String -> String -> Aff (Either String String)
callTool server tool input = notImplemented "Server.Routes.Mcp.callTool"
