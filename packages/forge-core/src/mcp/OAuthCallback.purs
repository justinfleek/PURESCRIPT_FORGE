-- | MCP OAuth Callback
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/mcp/oauth-callback.ts
module Forge.MCP.OAuthCallback where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Forge.Util.NotImplemented (notImplemented)

-- | Handle OAuth callback
handleCallback :: String -> String -> Aff (Either String Unit)
handleCallback code state = notImplemented "MCP.OAuthCallback.handleCallback"
