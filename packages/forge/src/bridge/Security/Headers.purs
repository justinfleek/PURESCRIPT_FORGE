-- | Security Headers - HTTP Security Headers Middleware
-- | CSP, X-Frame-Options, X-Content-Type-Options, HSTS, X-XSS-Protection
module Bridge.Security.Headers where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe, fromMaybe)
import Bridge.FFI.Node.Express (Response)

-- | Security headers configuration
type SecurityHeadersConfig =
  { contentSecurityPolicy :: String
  , frameOptions :: String
  , contentTypeOptions :: String
  , strictTransportSecurity :: String
  , xssProtection :: String
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

-- | FFI declarations (top-level)
foreign import addSecurityHeadersImpl :: Response -> SecurityHeadersConfig -> Effect Unit
foreign import setHeader :: Response -> String -> String -> Effect Unit

-- | Add security headers to response
addSecurityHeaders :: Response -> Maybe SecurityHeadersConfig -> Effect Unit
addSecurityHeaders response config =
  addSecurityHeadersImpl response (fromMaybe defaultSecurityHeaders config)

-- | Set Content-Security-Policy header
setContentSecurityPolicy :: Response -> String -> Effect Unit
setContentSecurityPolicy response policy =
  setHeader response "Content-Security-Policy" policy

-- | Set X-Frame-Options header
setFrameOptions :: Response -> String -> Effect Unit
setFrameOptions response value =
  setHeader response "X-Frame-Options" value

-- | Set X-Content-Type-Options header
setContentTypeOptions :: Response -> Effect Unit
setContentTypeOptions response =
  setHeader response "X-Content-Type-Options" "nosniff"

-- | Set Strict-Transport-Security header
setStrictTransportSecurity :: Response -> Int -> Boolean -> Effect Unit
setStrictTransportSecurity response maxAge includeSubDomains =
  let value = "max-age=" <> show maxAge <> (if includeSubDomains then "; includeSubDomains" else "")
  in setHeader response "Strict-Transport-Security" value
