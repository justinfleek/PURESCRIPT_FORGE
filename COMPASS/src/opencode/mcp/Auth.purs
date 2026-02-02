-- | MCP Authentication
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/mcp/auth.ts
module Opencode.MCP.Auth where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

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
