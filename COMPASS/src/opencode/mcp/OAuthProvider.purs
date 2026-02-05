-- | MCP OAuth Provider
module Opencode.MCP.OAuthProvider where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.Array as Array
import Bridge.FFI.Node.Fetch as Fetch

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
getAuthUrl config state =
  let scopesParam = String.joinWith "+" config.scopes
      params = Array.filter (not <<< String.null)
        [ "client_id=" <> encodeURIComponent config.clientId
        , "redirect_uri=" <> encodeURIComponent "http://localhost:3000/oauth/callback"
        , "response_type=code"
        , "scope=" <> encodeURIComponent scopesParam
        , "state=" <> encodeURIComponent state
        ]
      queryString = String.joinWith "&" params
  in config.authUrl <> (if String.contains (String.Pattern "?") config.authUrl then "&" else "?") <> queryString
  where
    foreign import encodeURIComponent :: String -> String

-- | Exchange code for token
exchangeCode :: OAuthConfig -> String -> Aff (Either String String)
exchangeCode config code = do
  let body = String.joinWith "&"
        [ "grant_type=authorization_code"
        , "code=" <> encodeURIComponent code
        , "client_id=" <> encodeURIComponent config.clientId
        , "redirect_uri=" <> encodeURIComponent "http://localhost:3000/oauth/callback"
        ] <> (case config.clientSecret of
          Just secret -> "&client_secret=" <> encodeURIComponent secret
          Nothing -> "")
  
  let options =
        { method: "POST"
        , headers:
            [ { key: "Content-Type", value: "application/x-www-form-urlencoded" }
            , { key: "Accept", value: "application/json" }
            ]
        , body: Just body
        }
  
  result <- Fetch.fetch config.tokenUrl options
  case result of
    Left err -> pure $ Left ("Token exchange failed: " <> err)
    Right response -> do
      isOk <- liftEffect $ Fetch.ok response
      if not isOk
        then do
          statusCode <- liftEffect $ Fetch.status response
          pure $ Left ("HTTP " <> show statusCode)
        else do
          textResult <- Fetch.text response
          case textResult of
            Left err -> pure $ Left ("Failed to read response: " <> err)
            Right body -> pure $ Right body
