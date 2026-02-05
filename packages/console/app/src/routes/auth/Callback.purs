-- | Auth Callback Route Handler
-- |
-- | Handles OAuth callback, exchanges code for tokens, updates session.
-- | PureScript wrapper around SolidJS Start route handler.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/auth/[...callback].ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Auth.Callback
  ( handleCallback
  , CallbackError(..)
  ) where

import Prelude

import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Map as Map
import Console.App.FFI.SolidStart (APIEvent, getRequestUrl, getSearchParams, getSearchParam, redirect, textResponse)
import Console.App.Context.Auth (AuthClient, AccountInfo)
import Console.App.Context.AuthSession (useAuthSession)

-- | Callback error
data CallbackError
  = NoCode
  | ExchangeError String
  | DecodeError String
  | OtherError String

derive instance eqCallbackError :: Eq CallbackError

instance showCallbackError :: Show CallbackError where
  show NoCode = "NoCode"
  show (ExchangeError msg) = "ExchangeError(" <> msg <> ")"
  show (DecodeError msg) = "DecodeError(" <> msg <> ")"
  show (OtherError msg) = "OtherError(" <> msg <> ")"

-- | FFI: Exchange authorization code for tokens
foreign import authClientExchange :: String -> String -> String -> Aff { err :: Maybe String, tokens :: { access :: String } }

-- | FFI: Decode access token
foreign import authClientDecode :: String -> String -> Aff { err :: Maybe String, subject :: { properties :: { accountID :: String, email :: String } } }

-- | Handle auth callback route
handleCallback :: APIEvent -> AuthClient -> Aff Response
handleCallback event client = do
  request <- liftEffect (getRequest event)
  url <- liftEffect (getRequestUrl request)
  searchParams <- liftEffect (getSearchParams url)
  codeParam <- liftEffect (getSearchParam searchParams "code")
  
  case codeParam of
    Nothing -> do
      -- Return error response
      let errorJson = "{\"error\":\"No code found\",\"cause\":{}}"
      textResponse errorJson 500
    
    Just code -> do
      -- Exchange code for tokens
      exchangeResult <- authClientExchange client.clientID client.issuer code
      
      case exchangeResult.err of
        Just err -> do
          let errorJson = "{\"error\":\"" <> err <> "\",\"cause\":{}}"
          textResponse errorJson 500
        
        Nothing -> do
          -- Decode access token
          decodeResult <- authClientDecode client.clientID exchangeResult.tokens.access
          
          case decodeResult.err of
            Just err -> do
              let errorJson = "{\"error\":\"" <> err <> "\",\"cause\":{}}"
              textResponse errorJson 500
            
            Nothing -> do
              -- Update session
              session <- useAuthSession
              let accountId = decodeResult.subject.properties.accountID
              let email = decodeResult.subject.properties.email
              
              -- Update session with new account
              let accountInfo :: AccountInfo = { id: accountId, email: email }
              session.update \value ->
                value
                  { account = Map.insert accountId accountInfo value.account
                  , current = Just accountId
                  }
              
              -- Determine redirect URL
              let callbackPath = url.pathname
              let redirectPath = if callbackPath == "/auth/callback"
                    then "/auth"
                    else callbackPath.replace("/auth/callback", "")
              
              redirect redirectPath
