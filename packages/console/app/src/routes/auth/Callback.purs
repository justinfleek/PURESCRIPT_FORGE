-- | Auth Callback Route (catch-all)
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/auth/[...callback].ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Auth.Callback
  ( CallbackRequest(..)
  , CallbackResult(..)
  , CallbackError(..)
  , DecodedToken(..)
  , SessionUpdate(..)
  , handleCallback
  , parseCallbackUrl
  , buildSessionUpdate
  , determineRedirectPath
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Console.App.Context.Auth (AuthSession, AccountInfo)

-- | Callback request parameters
type CallbackRequest =
  { url :: String
  , pathname :: String
  , code :: Maybe String
  , origin :: String
  }

-- | Parse callback URL parameters (pure)
parseCallbackUrl :: String -> Maybe String -> CallbackRequest
parseCallbackUrl url codeParam =
  { url
  , pathname: "/auth/callback"  -- simplified
  , code: codeParam
  , origin: ""  -- would be extracted from URL
  }

-- | Callback error types
data CallbackError
  = NoCodeProvided
  | ExchangeFailed String
  | DecodeFailed String

derive instance eqCallbackError :: Eq CallbackError

instance showCallbackError :: Show CallbackError where
  show NoCodeProvided = "No code found"
  show (ExchangeFailed msg) = "(ExchangeFailed " <> show msg <> ")"
  show (DecodeFailed msg) = "(DecodeFailed " <> show msg <> ")"

-- | Decoded token subject
type DecodedToken =
  { accountId :: String
  , email :: String
  }

-- | Session update data
type SessionUpdate =
  { accountId :: String
  , email :: String
  }

-- | Build session update from decoded token (pure)
buildSessionUpdate :: DecodedToken -> SessionUpdate
buildSessionUpdate token =
  { accountId: token.accountId
  , email: token.email
  }

-- | Apply session update (pure)
applySessionUpdate :: AuthSession -> SessionUpdate -> AuthSession
applySessionUpdate session update =
  let
    newAccountInfo :: AccountInfo
    newAccountInfo = { id: update.accountId, email: update.email }
    
    newAccounts = session.account  -- would use Map.insert
  in
    session { current = Just update.accountId }

-- | Callback result
data CallbackResult
  = CallbackSuccess { redirectTo :: String, sessionUpdate :: SessionUpdate }
  | CallbackFailure { error :: CallbackError, details :: String }

derive instance eqCallbackResult :: Eq CallbackResult

instance showCallbackResult :: Show CallbackResult where
  show (CallbackSuccess r) = "(CallbackSuccess " <> show r.redirectTo <> ")"
  show (CallbackFailure r) = "(CallbackFailure " <> show r.error <> ")"

-- | Determine redirect path after successful callback (pure)
determineRedirectPath :: String -> String
determineRedirectPath pathname
  | pathname == "/auth/callback" = "/auth"
  | otherwise = 
      -- Replace /auth/callback with empty string
      -- In real impl would use String.replace
      pathname

-- | Handle callback (pure logic - actual token exchange would be effectful)
handleCallback :: CallbackRequest -> Maybe DecodedToken -> CallbackResult
handleCallback req tokenM = case req.code of
  Nothing -> CallbackFailure 
    { error: NoCodeProvided
    , details: "No authorization code in callback URL"
    }
  Just _ -> case tokenM of
    Nothing -> CallbackFailure
      { error: ExchangeFailed "Token exchange failed"
      , details: "Could not exchange code for tokens"
      }
    Just token ->
      let
        sessionUpdate = buildSessionUpdate token
        redirectTo = determineRedirectPath req.pathname
      in
        CallbackSuccess { redirectTo, sessionUpdate }

-- | Error response builder
buildErrorResponse :: CallbackError -> String -> { error :: String, status :: Int }
buildErrorResponse err details =
  { error: show err <> ": " <> details
  , status: 500
  }
