-- | MCP OAuth Provider
-- | 1:1 parity with opencode-dev/packages/opencode/src/mcp/oauth-provider.ts
module Forge.MCP.OAuthProvider where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe(..))

type OAuthConfig =
  { clientId :: String
  , clientSecret :: Maybe String
  , authUrl :: String
  , tokenUrl :: String
  , scopes :: Array String
  }

-- | Build OAuth authorization URL with proper parameter encoding
foreign import buildAuthUrlFFI :: String -> String -> Array String -> String -> String

-- | Exchange authorization code for access token via POST to token endpoint
foreign import exchangeCodeFFI :: String -> String -> String -> String -> Aff (Either String String)

-- | Get the OAuth authorization URL for a given config and state parameter
getAuthUrl :: OAuthConfig -> String -> String
getAuthUrl config state = buildAuthUrlFFI config.authUrl config.clientId config.scopes state

-- | Exchange an authorization code for an access token
exchangeCode :: OAuthConfig -> String -> Aff (Either String String)
exchangeCode config code = do
  let secret = case config.clientSecret of
        Just s -> s
        Nothing -> ""
  exchangeCodeFFI config.tokenUrl config.clientId secret code
