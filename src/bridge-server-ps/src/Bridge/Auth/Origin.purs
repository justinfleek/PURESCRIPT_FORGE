-- | Origin Validation - WebSocket Origin Header Validation
-- |
-- | **What:** Validates WebSocket connection origin headers to prevent unauthorized
-- |         connections from malicious websites. Implements origin allowlist.
-- | **Why:** Prevents cross-site WebSocket hijacking attacks. Ensures only trusted
-- |         origins can connect to the WebSocket server.
-- | **How:** Extracts origin header from WebSocket upgrade request, checks against
-- |         allowlist of permitted origins. Rejects connections from unauthorized origins.
-- |
-- | **Dependencies:**
-- | - `Bridge.FFI.Node.Http`: HTTP request headers
-- | - `Bridge.FFI.Node.Pino`: Structured logging
-- |
-- | **Mathematical Foundation:**
-- | - **Origin Format:** `scheme://host[:port]` (e.g., `http://localhost:3000`)
-- | - **Validation:** Origin valid iff `elem origin allowedOrigins`
-- | - **Wildcard Support:** `*` allows all origins (development only)
-- |
-- | **Security Properties:**
-- | - Only allowed origins can connect
-- | - Wildcard disabled in production
-- | - Origin header validated on every connection
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Bridge.Auth.Origin as Origin
-- |
-- | -- Validate origin
-- | isValid <- Origin.validateOrigin origin allowedOrigins
-- | if isValid then
-- |   -- Allow connection
-- | else
-- |   -- Reject connection
-- | ```
module Bridge.Auth.Origin where

import Prelude
import Data.Array (elem, uncons)
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.String (toLower)
import Bridge.FFI.Node.Pino (Logger)

-- | Allowed origins configuration
type AllowedOrigins =
  { origins :: Array String
  , allowWildcard :: Boolean -- Only true in development
  }

-- | Default allowed origins (development)
defaultAllowedOrigins :: AllowedOrigins
defaultAllowedOrigins =
  { origins: [
      "http://localhost:3000"
      , "http://localhost:8765"
      , "http://127.0.0.1:3000"
      , "http://127.0.0.1:8765"
    ]
  , allowWildcard: false -- Never allow wildcard in production
  }

-- | Validate origin
-- |
-- | **Purpose:** Checks if origin is in allowlist.
-- | **Parameters:**
-- | - `origin`: Origin header value (e.g., "http://localhost:3000")
-- | - `allowedOrigins`: Allowed origins configuration
-- | **Returns:** True if origin is allowed, false otherwise
-- |
-- | **Logic:**
-- | - If wildcard allowed and origin is "*", return true (development only)
-- | - Check if origin is in allowedOrigins.origins array
-- | - Return false if not found
validateOrigin :: String -> AllowedOrigins -> Boolean
validateOrigin origin allowedOrigins = do
  if allowedOrigins.allowWildcard && origin == "*" then
    true
  else
    elem origin allowedOrigins.origins

-- | Extract origin from request headers
-- |
-- | **Purpose:** Gets origin header value from HTTP request.
-- | **Parameters:**
-- | - `headers`: HTTP request headers
-- | **Returns:** Maybe origin string
extractOrigin :: Array { key :: String, value :: String } -> Maybe String
extractOrigin headers = findOrigin headers
  where
    findOrigin :: Array { key :: String, value :: String } -> Maybe String
    findOrigin arr = case uncons arr of
      Nothing -> Nothing
      Just { head: h, tail: hs } ->
        if toLower h.key == "origin" then
          Just h.value
        else
          findOrigin hs

-- | Validate origin from request
-- |
-- | **Purpose:** Validates origin from HTTP request headers.
-- | **Parameters:**
-- | - `headers`: HTTP request headers
-- | - `allowedOrigins`: Allowed origins configuration
-- | - `logger`: Logger for error reporting
-- | **Returns:** Either error message or validated origin
validateOriginFromRequest :: Array { key :: String, value :: String } -> AllowedOrigins -> Logger -> Either String String
validateOriginFromRequest headers allowedOrigins _logger =
  case extractOrigin headers of
    Just origin -> do
      if validateOrigin origin allowedOrigins then
        Right origin
      else
        Left ("Origin not allowed: " <> origin)
    Nothing -> do
      -- In production, require origin header
      if allowedOrigins.allowWildcard then
        Right "*" -- Development: allow missing origin
      else
        Left "Origin header required"
