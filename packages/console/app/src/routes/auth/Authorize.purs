-- | Auth Authorize Route Handler
-- |
-- | Initiates OAuth authorization flow.
-- | PureScript wrapper around SolidJS Start route handler.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/auth/authorize.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Auth.Authorize
  ( handleAuthorize
  , AuthorizeParams
  ) where

import Prelude

import Effect.Aff (Aff)
import Data.Maybe (Maybe(..))
import Console.App.FFI.SolidStart (APIEvent, getRequestUrl, getSearchParams, getSearchParam, createURL)
import Console.App.Context.Auth (AuthClient)
import Effect.Class (liftEffect)

-- | Authorize parameters
type AuthorizeParams =
  { continue :: Maybe String
  }

-- | FFI: Auth client authorize function
foreign import authClientAuthorize :: String -> String -> String -> Aff String

-- | Handle auth authorize route
-- | Builds callback URL and redirects to OAuth provider
handleAuthorize :: APIEvent -> AuthClient -> Aff Response
handleAuthorize event client = do
  request <- liftEffect (getRequest event)
  url <- liftEffect (getRequestUrl request)
  searchParams <- liftEffect (getSearchParams url)
  continueParam <- liftEffect (getSearchParam searchParams "continue")
  
  let continuePath = case continueParam of
        Just path -> path
        Nothing -> ""
  
  -- Build callback URL
  callbackUrl <- liftEffect $ createURL $ "./callback" <> continuePath
  
  -- Get authorization URL from auth client
  authUrl <- authClientAuthorize client.clientID client.issuer callbackUrl
  
  -- Redirect to auth URL
  redirect authUrl
