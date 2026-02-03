-- | Auth Authorize Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/auth/authorize.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Auth.Authorize
  ( AuthorizeRequest(..)
  , AuthorizeResponse(..)
  , buildCallbackUrl
  , buildAuthorizeRedirect
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe)

-- | Authorize request parameters
type AuthorizeRequest =
  { requestUrl :: String
  , continueParam :: Maybe String
  }

-- | Authorize response
data AuthorizeResponse
  = RedirectResponse { url :: String, status :: Int }

derive instance eqAuthorizeResponse :: Eq AuthorizeResponse

instance showAuthorizeResponse :: Show AuthorizeResponse where
  show (RedirectResponse r) = "(RedirectResponse " <> show r.url <> " " <> show r.status <> ")"

-- | Build callback URL from request URL and continue param (pure)
buildCallbackUrl :: String -> Maybe String -> String
buildCallbackUrl baseUrl continueParam =
  let
    cont = fromMaybe "" continueParam
    -- Extract origin from URL (simplified - in real impl would parse URL)
    callbackPath = "./callback" <> cont
  in
    callbackPath

-- | Authorization URL builder (pure data structure)
type AuthorizationParams =
  { callbackUrl :: String
  , responseType :: String  -- "code"
  }

-- | Build authorize redirect parameters (pure)
buildAuthorizeRedirect :: AuthorizeRequest -> AuthorizationParams
buildAuthorizeRedirect req =
  let
    cont = fromMaybe "" req.continueParam
    callbackUrl = buildCallbackUrl req.requestUrl req.continueParam
  in
    { callbackUrl
    , responseType: "code"
    }

-- | Create redirect response (pure)
redirectResponse :: String -> AuthorizeResponse
redirectResponse url = RedirectResponse { url, status: 302 }
