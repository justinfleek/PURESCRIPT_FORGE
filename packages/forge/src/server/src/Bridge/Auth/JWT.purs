-- | JWT Authentication - JSON Web Token Generation and Validation
-- |
-- | **What:** Provides JWT token generation, validation, and decoding for authentication.
-- |         Uses Node.js `jose` library via FFI for production-grade JWT handling.
-- | **Why:** Secure, stateless authentication that can be verified without database lookups.
-- |         Standard JWT format ensures interoperability and security best practices.
-- | **How:** Generates signed JWT tokens with claims (user ID, roles, expiration).
-- |         Validates tokens by verifying signature and expiration. Decodes tokens
-- |         to extract claims for authorization decisions.
-- |
-- | **Dependencies:**
-- | - Node.js `jose` library (via FFI)
-- | - `Bridge.Auth.RBAC`: Role-based access control
-- | - `Bridge.FFI.Node.Pino`: Structured logging
-- |
-- | **Mathematical Foundation:**
-- | - **JWT Structure:** `header.payload.signature`
-- |   - Header: `{ alg: "HS256", typ: "JWT" }`
-- |   - Payload: `{ sub: String, roles: Array String, exp: Int, iat: Int }`
-- |   - Signature: HMAC-SHA256(header + "." + payload, secret)
-- | - **Token Expiration:** Tokens expire after `TOKEN_EXPIRY_SECONDS` (default: 24 hours)
-- | - **Signature Verification:** Token is valid iff signature matches and expiration not passed
-- |
-- | **Security Properties:**
-- | - Tokens are signed with secret key (never exposed to client)
-- | - Expiration enforced server-side
-- | - Roles embedded in token (cannot be modified without invalidating signature)
-- | - Secret key rotation supported (via environment variable)
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Bridge.Auth.JWT as JWT
-- |
-- | -- Generate token for user
-- | token <- JWT.generateToken { userId: "user-123", roles: ["user"] }
-- |
-- | -- Validate token
-- | result <- JWT.validateToken token
-- | case result of
-- |   Right claims -> -- Token valid, use claims
-- |   Left err -> -- Token invalid
-- | ```
module Bridge.Auth.JWT where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, liftEffect, makeAff, nonCanceler)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Argonaut (Json, JsonDecodeError, decodeJson, encodeJson, (.?), (:=), (~>))
import Data.Argonaut as A
import Data.DateTime (DateTime)
import Data.DateTime.Instant (Instant, instant, toDateTime)
import Data.Time.Duration (Seconds(..))
import Data.Newtype (unwrap)
import Bridge.FFI.Node.Pino (Logger)

-- | JWT Claims - Token payload
-- |
-- | **Purpose:** Contains user identity and authorization information embedded in JWT.
-- | **Fields:**
-- | - `sub`: Subject (user ID)
-- | - `roles`: Array of role names (e.g., ["user", "admin"])
-- | - `exp`: Expiration timestamp (Unix epoch seconds)
-- | - `iat`: Issued at timestamp (Unix epoch seconds)
-- | - `jti`: JWT ID (unique token identifier)
type Claims =
  { sub :: String
  , roles :: Array String
  , exp :: Int
  , iat :: Int
  , jti :: String
  }

-- | Token generation options
type TokenOptions =
  { userId :: String
  , roles :: Array String
  , expiresIn :: Maybe Seconds -- Default: 24 hours
  }

-- | Token validation result
type TokenValidationResult =
  { valid :: Boolean
  , claims :: Maybe Claims
  , error :: Maybe String
  }

-- | Generate JWT token
-- |
-- | **Purpose:** Creates a signed JWT token with user claims.
-- | **Parameters:**
-- | - `options`: User ID, roles, and expiration
-- | - `logger`: Logger for error reporting
-- | **Returns:** Signed JWT token string
-- | **Side Effects:** Generates random JWT ID, gets current time
-- |
-- | **Example:**
-- | ```purescript
-- | token <- generateToken { userId: "user-123", roles: ["user"], expiresIn: Nothing } logger
-- | ```
generateToken :: TokenOptions -> Logger -> Aff (Either String String)
generateToken options logger = do
  result <- fromEffectFnAff $ generateTokenImpl options
  pure result
  where
    foreign import generateTokenImpl :: TokenOptions -> EffectFnAff (Either String String)

-- | Validate JWT token
-- |
-- | **Purpose:** Verifies token signature and expiration, extracts claims.
-- | **Parameters:**
-- | - `token`: JWT token string
-- | - `logger`: Logger for error reporting
-- | **Returns:** Either error message or validated claims
-- | **Side Effects:** Verifies signature, checks expiration
-- |
-- | **Example:**
-- | ```purescript
-- | result <- validateToken token logger
-- | case result of
-- |   Right claims -> -- Token valid
-- |   Left err -> -- Token invalid: err
-- | ```
validateToken :: String -> Logger -> Aff (Either String Claims)
validateToken token logger = do
  result <- fromEffectFnAff $ validateTokenImpl token
  case result.valid of
    true -> case result.claims of
      Just claims -> pure (Right claims)
      Nothing -> pure (Left "Token validation failed: no claims")
    false -> pure (Left (result.error # fromMaybe "Token validation failed"))
  where
    foreign import validateTokenImpl :: String -> EffectFnAff TokenValidationResult

-- | Decode JWT token (without validation)
-- |
-- | **Purpose:** Extracts claims from token without verifying signature.
-- | **WARNING:** Only use for debugging or when signature verification is done separately.
-- | **Parameters:**
-- | - `token`: JWT token string
-- | **Returns:** Either error or decoded claims
decodeToken :: String -> Either String Claims
decodeToken token = decodeTokenImpl token
  where
    foreign import decodeTokenImpl :: String -> Either String Claims

-- | Get token expiration time
-- |
-- | **Purpose:** Extracts expiration timestamp from token.
-- | **Parameters:**
-- | - `token`: JWT token string
-- | **Returns:** Either error or expiration timestamp (Unix epoch seconds)
getTokenExpiration :: String -> Either String Int
getTokenExpiration token = do
  claims <- decodeToken token
  pure claims.exp

-- | Check if token is expired
-- |
-- | **Purpose:** Determines if token has passed its expiration time.
-- | **Parameters:**
-- | - `token`: JWT token string
-- | **Returns:** Either error or boolean (true if expired)
isTokenExpired :: String -> Either String Boolean
isTokenExpired token = do
  exp <- getTokenExpiration token
  now <- liftEffect $ getCurrentUnixTime
  pure (exp < now)
  where
    foreign import getCurrentUnixTime :: Effect Int

-- | Claims JSON codec
instance claimsJson :: A.EncodeJson Claims where
  encodeJson claims =
    "sub" := claims.sub
    ~> "roles" := claims.roles
    ~> "exp" := claims.exp
    ~> "iat" := claims.iat
    ~> "jti" := claims.jti

instance claimsJsonDecode :: A.DecodeJson Claims where
  decodeJson json = do
    obj <- A.decodeJson json
    sub <- obj .? "sub"
    roles <- obj .? "roles"
    exp <- obj .? "exp"
    iat <- obj .? "iat"
    jti <- obj .? "jti"
    pure { sub, roles, exp, iat, jti }
