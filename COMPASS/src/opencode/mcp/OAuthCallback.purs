-- | MCP OAuth Callback
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/mcp/oauth-callback.ts
module Opencode.MCP.OAuthCallback where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

-- | Handle OAuth callback
handleCallback :: String -> String -> Aff (Either String Unit)
handleCallback code state = notImplemented "MCP.OAuthCallback.handleCallback"
