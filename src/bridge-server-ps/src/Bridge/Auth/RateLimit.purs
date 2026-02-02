-- | Rate Limiting - Per-User Request Rate Limiting
-- |
-- | **What:** Implements rate limiting per authenticated user to prevent abuse.
-- |         Tracks request counts per user within time windows.
-- | **Why:** Prevents API abuse, ensures fair resource usage, protects against
-- |         denial-of-service attacks. Enforces usage quotas per user.
-- | **How:** Uses token bucket algorithm with per-user buckets. Tracks requests
-- |         in memory (or Redis in production) with sliding window.
-- |
-- | **Dependencies:**
-- | - `Bridge.Auth.JWT`: User identification from claims
-- | - `Bridge.FFI.Node.Pino`: Structured logging
-- |
-- | **Mathematical Foundation:**
-- | - **Token Bucket:** Each user has bucket with capacity `maxRequests` and
-- |   refill rate `refillRate` requests per `windowSeconds`.
-- | - **Rate Limit:** Request allowed iff `tokens > 0`, then `tokens = tokens - 1`
-- | - **Refill:** `tokens = min(maxRequests, tokens + refillRate * elapsed / windowSeconds)`
-- |
-- | **Security Properties:**
-- | - Rate limits enforced per user (not per IP)
-- | - Limits reset after window expires
-- | - Different limits for different operations
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Bridge.Auth.RateLimit as RateLimit
-- |
-- | -- Check rate limit
-- | result <- RateLimit.checkRateLimit userId "venice.chat" rateLimiter
-- | case result of
-- |   Right allowed -> -- Request allowed
-- |   Left err -> -- Rate limit exceeded
-- | ```
module Bridge.Auth.RateLimit where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Ref (Ref, new, read, write, modify)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Map (Map)
import Data.Map as Map
import Data.DateTime (DateTime)
import Data.DateTime.Instant (Instant)
import Data.Tuple (Tuple(..))
import Bridge.FFI.Node.Pino (Logger)

-- | FFI: Check rate limit implementation
foreign import checkRateLimitImpl :: String -> String -> RateLimiter -> Effect (Either String RateLimitResult)

-- | FFI: Reset rate limit implementation
foreign import resetRateLimitImpl :: String -> String -> RateLimiter -> Effect (Either String Unit)

-- | FFI: Get rate limit status implementation
foreign import getRateLimitStatusImpl :: String -> String -> RateLimiter -> Effect RateLimitResult

-- | Rate limit configuration
type RateLimitConfig =
  { maxRequests :: Int
  , windowSeconds :: Int
  , refillRate :: Int -- Requests per window
  }

-- | Token bucket state
type TokenBucket =
  { tokens :: Int
  , lastRefill :: Instant
  }

-- | Rate limiter state
type RateLimiter =
  { buckets :: Ref (Map String TokenBucket)
  , configs :: Map String RateLimitConfig
  , logger :: Logger
  }

-- | Rate limit result
type RateLimitResult =
  { allowed :: Boolean
  , remaining :: Int
  , resetAt :: Maybe Instant
  , error :: Maybe String
  }

-- | Default rate limit configurations
defaultConfigs :: Map String RateLimitConfig
defaultConfigs = Map.fromFoldable [
  Tuple "venice.chat" { maxRequests: 100, windowSeconds: 3600, refillRate: 100 }
  , Tuple "venice.models" { maxRequests: 50, windowSeconds: 3600, refillRate: 50 }
  , Tuple "venice.image" { maxRequests: 20, windowSeconds: 3600, refillRate: 20 }
  , Tuple "lean.check" { maxRequests: 200, windowSeconds: 3600, refillRate: 200 }
  , Tuple "session.create" { maxRequests: 10, windowSeconds: 3600, refillRate: 10 }
]

-- | Create rate limiter
-- |
-- | **Purpose:** Creates a new rate limiter instance.
-- | **Parameters:**
-- | - `configs`: Map of operation -> rate limit config (uses defaults if not provided)
-- | - `logger`: Logger
-- | **Returns:** Rate limiter instance
createRateLimiter :: Maybe (Map String RateLimitConfig) -> Logger -> Effect RateLimiter
createRateLimiter configs logger = do
  buckets <- new Map.empty
  let finalConfigs = fromMaybe defaultConfigs configs
  pure { buckets, configs: finalConfigs, logger }

-- | Check rate limit
-- |
-- | **Purpose:** Checks if user can make request for operation.
-- | **Parameters:**
-- | - `userId`: User identifier
-- | - `operation`: Operation identifier (e.g., "venice.chat")
-- | - `rateLimiter`: Rate limiter instance
-- | **Returns:** Either error or rate limit result
checkRateLimit :: String -> String -> RateLimiter -> Aff (Either String RateLimitResult)
checkRateLimit userId operation rateLimiter = do
  liftEffect $ checkRateLimitImpl userId operation rateLimiter

-- | Reset rate limit for user
-- |
-- | **Purpose:** Resets rate limit bucket for user (admin operation).
-- | **Parameters:**
-- | - `userId`: User identifier
-- | - `operation`: Operation identifier
-- | - `rateLimiter`: Rate limiter instance
-- | **Returns:** Success or error
resetRateLimit :: String -> String -> RateLimiter -> Effect (Either String Unit)
resetRateLimit userId operation rateLimiter =
  resetRateLimitImpl userId operation rateLimiter

-- | Get rate limit status
-- |
-- | **Purpose:** Returns current rate limit status for user.
-- | **Parameters:**
-- | - `userId`: User identifier
-- | - `operation`: Operation identifier
-- | - `rateLimiter`: Rate limiter instance
-- | **Returns:** Rate limit result
getRateLimitStatus :: String -> String -> RateLimiter -> Effect RateLimitResult
getRateLimitStatus userId operation rateLimiter =
  getRateLimitStatusImpl userId operation rateLimiter
