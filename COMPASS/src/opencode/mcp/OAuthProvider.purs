-- | MCP OAuth Provider
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/mcp/oauth-provider.ts
module Opencode.MCP.OAuthProvider where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | OAuth configuration
type OAuthConfig =
  { clientId :: String
  , clientSecret :: Maybe String
  , authUrl :: String
  , tokenUrl :: String
  , scopes :: Array String
  }

-- | Get authorization URL
getAuthUrl :: OAuthConfig -> String -> String
getAuthUrl config state = "" -- TODO: Implement

-- | Exchange code for token
exchangeCode :: OAuthConfig -> String -> Aff (Either String String)
exchangeCode config code = notImplemented "MCP.OAuthProvider.exchangeCode"
