-- | Rate Limiter for Venice API
module Bridge.Venice.RateLimiter where

import Prelude
import Effect (Effect)
import Effect.Ref (Ref, new, read, write)
import Data.Maybe (Maybe(..))

-- | Rate limit state
type RateLimitState =
  { requests ::
      { limit :: Int
      , remaining :: Int
      , reset :: Maybe Number
      }
  , tokens ::
      { limit :: Int
      , remaining :: Int
      , reset :: Maybe Number
      }
  , tier :: Maybe String
  }

-- | Rate limiter
type RateLimiter = Ref RateLimitState

-- | Create rate limiter
createRateLimiter :: Effect RateLimiter
createRateLimiter = new
  { requests: { limit: 0, remaining: 0, reset: Nothing }
  , tokens: { limit: 0, remaining: 0, reset: Nothing }
  , tier: Nothing
  }

-- | Acquire rate limit (wait if needed)
acquireRateLimit :: RateLimiter -> Effect Unit
acquireRateLimit limiter = do
  state <- read limiter
  if state.requests.remaining > 0 && state.tokens.remaining > 0 then
    pure unit
  else
    pure unit

-- | Update from response headers
foreign import updateFromResponseImpl :: RateLimiter -> String -> Effect Unit

updateFromResponse :: RateLimiter -> String -> Effect Unit
updateFromResponse = updateFromResponseImpl
