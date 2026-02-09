-- | Security Headers - HTTP Security Headers Middleware
-- |
-- | **What:** Adds security headers to HTTP responses to prevent common attacks
-- |         (XSS, clickjacking, MIME sniffing, etc.). Implements security best practices.
-- | **Why:** Prevents common web vulnerabilities. Protects users from XSS, clickjacking,
-- |         and other attacks. Required for production security.
-- | **How:** Adds security headers to all HTTP responses. Configurable header values.
-- |
-- | **Dependencies:**
-- | - `Bridge.FFI.Node.Http`: HTTP server
-- |
-- | **Security Headers:**
-- | - `Content-Security-Policy`: Prevents XSS attacks
-- | - `X-Frame-Options`: Prevents clickjacking
-- | - `X-Content-Type-Options`: Prevents MIME sniffing
-- | - `Strict-Transport-Security`: Enforces HTTPS
-- | - `X-XSS-Protection`: XSS protection (legacy)
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Bridge.Security.Headers as Headers
-- |
-- | -- Add security headers to response
-- | Headers.addSecurityHeaders response
-- | ```
module Bridge.Security.Headers where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe, fromMaybe)

-- | Opaque HTTP Response type
foreign import data HttpResponse :: Type

-- | FFI: Add security headers implementation
foreign import addSecurityHeadersImpl :: HttpResponse -> SecurityHeadersConfig -> Effect Unit

-- | FFI: Set response header
foreign import setHeader :: HttpResponse -> String -> String -> Effect Unit

-- | Security headers configuration
type SecurityHeadersConfig =
  { contentSecurityPolicy :: String
  , frameOptions :: String -- "DENY" | "SAMEORIGIN"
  , contentTypeOptions :: String -- "nosniff"
  , strictTransportSecurity :: String -- HSTS header value
  , xssProtection :: String -- "1; mode=block"
  }

-- | Default security headers configuration
defaultSecurityHeaders :: SecurityHeadersConfig
defaultSecurityHeaders =
  { contentSecurityPolicy: "default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline'"
  , frameOptions: "DENY"
  , contentTypeOptions: "nosniff"
  , strictTransportSecurity: "max-age=31536000; includeSubDomains"
  , xssProtection: "1; mode=block"
  }

-- | Add security headers to response
-- |
-- | **Purpose:** Adds all security headers to HTTP response.
-- | **Parameters:**
-- | - `response`: HTTP response object
-- | - `config`: Security headers configuration (uses defaults if not provided)
-- | **Side Effects:** Sets response headers
addSecurityHeaders :: HttpResponse -> Maybe SecurityHeadersConfig -> Effect Unit
addSecurityHeaders response config = do
  let finalConfig = fromMaybe defaultSecurityHeaders config
  addSecurityHeadersImpl response finalConfig

-- | Set Content-Security-Policy header
-- |
-- | **Purpose:** Sets CSP header to prevent XSS attacks.
-- | **Parameters:**
-- | - `response`: HTTP response
-- | - `policy`: CSP policy string
setContentSecurityPolicy :: HttpResponse -> String -> Effect Unit
setContentSecurityPolicy response policy = setHeader response "Content-Security-Policy" policy

-- | Set X-Frame-Options header
-- |
-- | **Purpose:** Sets X-Frame-Options to prevent clickjacking.
-- | **Parameters:**
-- | - `response`: HTTP response
-- | - `value`: "DENY" or "SAMEORIGIN"
setFrameOptions :: HttpResponse -> String -> Effect Unit
setFrameOptions response value = do
  setHeader response "X-Frame-Options" value

-- | Set X-Content-Type-Options header
-- |
-- | **Purpose:** Prevents MIME type sniffing.
-- | **Parameters:**
-- | - `response`: HTTP response
setContentTypeOptions :: HttpResponse -> Effect Unit
setContentTypeOptions response = do
  setHeader response "X-Content-Type-Options" "nosniff"

-- | Set Strict-Transport-Security header
-- |
-- | **Purpose:** Enforces HTTPS connections.
-- | **Parameters:**
-- | - `response`: HTTP response
-- | - `maxAge`: Max age in seconds
-- | - `includeSubDomains`: Include subdomains
setStrictTransportSecurity :: HttpResponse -> Int -> Boolean -> Effect Unit
setStrictTransportSecurity response maxAge includeSubDomains = do
  let value = "max-age=" <> show maxAge <> (if includeSubDomains then "; includeSubDomains" else "")
  setHeader response "Strict-Transport-Security" value
