-- | Rate Limiting - Per-User Request Rate Limiting
-- |
-- | Implements rate limiting per authenticated user to prevent abuse.
-- | Uses token bucket algorithm with per-user buckets.
module Bridge.Auth.RateLimit where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Foreign.Object (Object)
import Foreign.Object as Object

-- | Rate limit configuration
type RateLimitConfig =
  { maxRequests :: Int
  , windowSeconds :: Int
  , refillRate :: Int
  }

-- | Token bucket state
type TokenBucket =
  { tokens :: Int
  , lastRefill :: Number
  }

-- | Rate limiter state
type RateLimiter =
  { buckets :: Ref (Object TokenBucket)
  , configs :: Object RateLimitConfig
  }

-- | Rate limit result
type RateLimitResult =
  { allowed :: Boolean
  , remaining :: Int
  , resetAt :: Maybe Number
  , error :: Maybe String
  }

-- | Default rate limit configurations
defaultConfigs :: Object RateLimitConfig
defaultConfigs = Object.fromFoldable
  [ Tuple "venice.chat" { maxRequests: 100, windowSeconds: 3600, refillRate: 100 }
  , Tuple "venice.models" { maxRequests: 50, windowSeconds: 3600, refillRate: 50 }
  , Tuple "venice.image" { maxRequests: 20, windowSeconds: 3600, refillRate: 20 }
  , Tuple "lean.check" { maxRequests: 200, windowSeconds: 3600, refillRate: 200 }
  , Tuple "session.create" { maxRequests: 10, windowSeconds: 3600, refillRate: 10 }
  ]

-- FFI declarations (top-level)
foreign import checkRateLimitImpl :: String -> String -> RateLimiter -> Effect (Either String RateLimitResult)
foreign import resetRateLimitImpl :: String -> String -> RateLimiter -> Effect (Either String Unit)
foreign import getRateLimitStatusImpl :: String -> String -> RateLimiter -> Effect RateLimitResult

-- | Create rate limiter
createRateLimiter :: Maybe (Object RateLimitConfig) -> Effect RateLimiter
createRateLimiter configs = do
  buckets <- createEmptyBuckets
  let finalConfigs = fromMaybe defaultConfigs configs
  pure { buckets, configs: finalConfigs }
  where
    foreign import createEmptyBuckets :: Effect (Ref (Object TokenBucket))

-- | Check rate limit for user operation
checkRateLimit :: String -> String -> RateLimiter -> Aff (Either String RateLimitResult)
checkRateLimit userId operation rateLimiter = do
  liftEffect $ checkRateLimitImpl userId operation rateLimiter
  where
    liftEffect = Effect.Class.liftEffect

-- | Reset rate limit for user (admin operation)
resetRateLimit :: String -> String -> RateLimiter -> Effect (Either String Unit)
resetRateLimit = resetRateLimitImpl

-- | Get rate limit status
getRateLimitStatus :: String -> String -> RateLimiter -> Effect RateLimitResult
getRateLimitStatus = getRateLimitStatusImpl
