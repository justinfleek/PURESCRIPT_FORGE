-- | MCP route
-- | 1:1 parity with opencode-dev/packages/opencode/src/server/routes/mcp.ts
module Forge.Server.Routes.Mcp where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe)
import Foreign (Foreign)

-- | List MCP servers
list :: Aff (Either String (Array Foreign))
list = listFFI

-- | Call a tool on an MCP server
callTool :: String -> String -> Foreign -> Aff (Either String Foreign)
callTool serverID toolName args = callToolFFI serverID toolName args

-- | Get server info
getServer :: String -> Aff (Either String (Maybe Foreign))
getServer serverID = getServerFFI serverID

-- | List tools for a server
listTools :: String -> Aff (Either String (Array Foreign))
listTools serverID = listToolsFFI serverID

foreign import listFFI :: Aff (Either String (Array Foreign))
foreign import callToolFFI :: String -> String -> Foreign -> Aff (Either String Foreign)
foreign import getServerFFI :: String -> Aff (Either String (Maybe Foreign))
foreign import listToolsFFI :: String -> Aff (Either String (Array Foreign))
