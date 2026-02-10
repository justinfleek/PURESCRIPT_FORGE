-- | Origin Validation - WebSocket Origin Header Validation
-- |
-- | Validates WebSocket connection origin headers to prevent unauthorized
-- | connections from malicious websites. Implements origin allowlist.
module Bridge.Auth.Origin where

import Prelude

import Data.Array (elem, findMap)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String (toLower)

-- | Allowed origins configuration
type AllowedOrigins =
  { origins :: Array String
  , allowWildcard :: Boolean
  }

-- | Default allowed origins (development)
defaultAllowedOrigins :: AllowedOrigins
defaultAllowedOrigins =
  { origins:
      [ "http://localhost:3000"
      , "http://localhost:8765"
      , "http://127.0.0.1:3000"
      , "http://127.0.0.1:8765"
      ]
  , allowWildcard: false
  }

-- | Validate origin against allowlist
validateOrigin :: String -> AllowedOrigins -> Boolean
validateOrigin origin allowedOrigins =
  if allowedOrigins.allowWildcard && origin == "*" then
    true
  else
    elem origin allowedOrigins.origins

-- | Extract origin from request headers
extractOrigin :: Array { key :: String, value :: String } -> Maybe String
extractOrigin headers =
  findMap (\h -> if toLower h.key == "origin" then Just h.value else Nothing) headers

-- | Validate origin from request headers
validateOriginFromRequest :: Array { key :: String, value :: String } -> AllowedOrigins -> Either String String
validateOriginFromRequest headers allowedOrigins =
  case extractOrigin headers of
    Just origin ->
      if validateOrigin origin allowedOrigins then
        Right origin
      else
        Left ("Origin not allowed: " <> origin)
    Nothing ->
      if allowedOrigins.allowWildcard then
        Right "*"
      else
        Left "Origin header required"
