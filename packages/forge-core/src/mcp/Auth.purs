-- | MCP Authentication
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/mcp/auth.ts
module Forge.MCP.Auth where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | MCP auth token
type MCPAuthToken =
  { token :: String
  , expiresAt :: Maybe Number
  }

-- | Authenticate with an MCP server
authenticate :: String -> Aff (Either String MCPAuthToken)
authenticate serverId = notImplemented "MCP.Auth.authenticate"

-- | Refresh token
refresh :: String -> Aff (Either String MCPAuthToken)
refresh serverId = notImplemented "MCP.Auth.refresh"
