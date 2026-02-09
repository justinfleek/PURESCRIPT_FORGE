-- | MCP OAuth Callback
-- | Ported from: opencode-dev/packages/opencode/src/mcp/oauth-callback.ts
-- | Based on COMPASS reference: opencode/mcp/OAuthProvider.purs
module Forge.MCP.OAuthCallback where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

-- | Handle OAuth callback with authorization code
-- | Exchanges the auth code for an access token
handleCallback :: String -> String -> Aff (Either String Unit)
handleCallback serverId code = do
  -- Validate inputs
  if String.null serverId then
    pure $ Left "Server ID is required"
  else if String.null code then
    pure $ Left "Authorization code is required"
  else
    fromEffectFnAff (handleOAuthCallbackFFI serverId code)

-- | FFI: Handle OAuth callback
foreign import handleOAuthCallbackFFI :: String -> String -> EffectFnAff (Either String Unit)
