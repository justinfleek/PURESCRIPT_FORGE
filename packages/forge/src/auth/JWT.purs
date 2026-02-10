-- | JWT Authentication - JSON Web Token Generation and Validation
-- |
-- | Uses Node.js `jose` library via FFI for production-grade JWT handling.
-- | Generates signed JWT tokens with claims (user ID, roles, expiration).
-- | Validates tokens by verifying signature and expiration.
module Bridge.Auth.JWT where

import Prelude

import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, (.:))
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)

-- | JWT Claims - Token payload
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
  , expiresInSeconds :: Maybe Int
  }

-- | Token validation result
type TokenValidationResult =
  { valid :: Boolean
  , claims :: Maybe Claims
  , error :: Maybe String
  }

-- FFI declarations (top-level, not in where blocks)
foreign import generateTokenImpl :: TokenOptions -> EffectFnAff (Either String String)
foreign import validateTokenImpl :: String -> EffectFnAff TokenValidationResult
foreign import decodeTokenImpl :: String -> Either String Claims
foreign import getCurrentUnixTime :: Effect Int

-- | Generate JWT token
-- | Creates a signed JWT token with user claims.
generateToken :: TokenOptions -> Aff (Either String String)
generateToken options = do
  result <- fromEffectFnAff $ generateTokenImpl options
  pure result

-- | Validate JWT token
-- | Verifies token signature and expiration, extracts claims.
validateToken :: String -> Aff (Either String Claims)
validateToken token = do
  result <- fromEffectFnAff $ validateTokenImpl token
  case result.valid of
    true -> case result.claims of
      Just claims -> pure (Right claims)
      Nothing -> pure (Left "Token validation failed: no claims")
    false -> pure (Left (fromMaybe "Token validation failed" result.error))

-- | Decode JWT token (without validation)
-- | WARNING: Only use for debugging or when signature verification is done separately.
decodeToken :: String -> Either String Claims
decodeToken = decodeTokenImpl

-- | Get token expiration time
getTokenExpiration :: String -> Either String Int
getTokenExpiration token = do
  claims <- decodeToken token
  pure claims.exp

-- | Claims JSON codec
instance encodeJsonClaims :: EncodeJson Claims where
  encodeJson claims = encodeJson
    { sub: claims.sub
    , roles: claims.roles
    , exp: claims.exp
    , iat: claims.iat
    , jti: claims.jti
    }

instance decodeJsonClaims :: DecodeJson Claims where
  decodeJson json = do
    obj <- decodeJson json
    sub <- obj .: "sub"
    roles <- obj .: "roles"
    exp <- obj .: "exp"
    iat <- obj .: "iat"
    jti <- obj .: "jti"
    pure { sub, roles, exp, iat, jti }
