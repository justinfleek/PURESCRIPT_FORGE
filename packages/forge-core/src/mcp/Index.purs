-- | MCP Index - main entry point
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/mcp/index.ts
module Forge.MCP.Index where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | MCP Server info
type MCPServer =
  { id :: String
  , name :: String
  , url :: String
  , tools :: Array String
  }

-- | Initialize MCP
init :: Aff (Either String Unit)
init = notImplemented "MCP.Index.init"

-- | List MCP servers
listServers :: Aff (Either String (Array MCPServer))
listServers = notImplemented "MCP.Index.listServers"

-- | Call an MCP tool
callTool :: String -> String -> String -> Aff (Either String String)
callTool serverId tool input = notImplemented "MCP.Index.callTool"
