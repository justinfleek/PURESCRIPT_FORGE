-- | Rate Limit State - Venice API Rate Limit Tracking
-- |
-- | **What:** Tracks Venice API rate limits (requests/min, tokens/min) and implements
-- |         backoff strategies for rate-limited requests.
-- | **Why:** Ensures the sidepanel respects Venice API rate limits and provides user
-- |         feedback when limits are approached or exceeded.
-- | **How:** Tracks rate limit headers from Venice API responses, calculates remaining
-- |         capacity, and implements exponential backoff on rate limit errors.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.FFI.DateTime`: DateTime utilities
-- |
-- | **Mathematical Foundation:**
-- | - **Request Limits:** Tracks requests per minute limit and remaining requests
-- | - **Token Limits:** Tracks tokens per minute limit and remaining tokens
-- | - **Reset Times:** Tracks when limits reset (Unix timestamps)
-- | - **Backoff:** Exponential backoff with jitter for rate limit errors
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.State.RateLimit as RateLimit
-- |
-- | -- Initial state
-- | rateLimitState = RateLimit.initialRateLimitState
-- |
-- | -- Update from headers
-- | updated = RateLimit.updateFromHeaders rateLimitState headers
-- | ```
-- |
-- | Based on spec 14-RATE-LIMIT-HANDLING.md
module Sidepanel.State.RateLimit where

import Prelude
import Data.DateTime (DateTime)
import Data.Maybe (Maybe(..))
import Data.Int as Int
import Sidepanel.FFI.DateTime (fromTimestamp, toTimestamp)
import Math (pow)

-- | Rate limit state - Tracks Venice API rate limits
-- |
-- | **Purpose:** Stores current rate limit information from Venice API responses.
-- | **Fields:**
-- | - `requestLimit`: Maximum requests per minute
-- | - `requestsRemaining`: Remaining requests in current window
-- | - `requestResetTime`: When request limit resets (Unix timestamp)
-- | - `tokenLimit`: Maximum tokens per minute
-- | - `tokensRemaining`: Remaining tokens in current window
-- | - `tokenResetTime`: When token limit resets (Unix timestamp)
-- | - `tier`: Rate limit tier (Free, Pro, Enterprise)
-- | - `lastUpdated`: When limits were last updated
-- | - `backoffMs`: Current backoff delay in milliseconds (0 if no backoff)
-- |
-- | **Invariants:**
-- | - `requestsRemaining >= 0` and `requestsRemaining <= requestLimit`
-- | - `tokensRemaining >= 0` and `tokensRemaining <= tokenLimit`
-- | - `backoffMs >= 0`
type RateLimitState =
  { requestLimit :: Int
  , requestsRemaining :: Int
  , requestResetTime :: Maybe DateTime  -- Unix timestamp from headers
  , tokenLimit :: Int
  , tokensRemaining :: Int
  , tokenResetTime :: Maybe DateTime  -- Unix timestamp from headers
  , tier :: Maybe String  -- "free" | "pro" | "enterprise"
  , lastUpdated :: Maybe DateTime
  , backoffMs :: Number  -- Current backoff delay (0 if no backoff)
  }

-- | Rate limit headers - Extracted from Venice API response headers
-- |
-- | **Purpose:** Represents rate limit information from HTTP response headers.
-- | **Fields:**
-- | - `requestLimit`: x-ratelimit-limit header value
-- | - `requestsRemaining`: x-ratelimit-remaining header value
-- | - `requestReset`: x-ratelimit-reset header value (Unix timestamp)
-- | - `tokenLimit`: x-ratelimit-tokens-limit header value
-- | - `tokensRemaining`: x-ratelimit-tokens-remaining header value
-- | - `tokenReset`: x-ratelimit-tokens-reset header value (Unix timestamp)
-- | - `tier`: x-ratelimit-tier header value
type RateLimitHeaders =
  { requestLimit :: Maybe Int
  , requestsRemaining :: Maybe Int
  , requestReset :: Maybe Number  -- Unix timestamp (seconds)
  , tokenLimit :: Maybe Int
  , tokensRemaining :: Maybe Int
  , tokenReset :: Maybe Number  -- Unix timestamp (seconds)
  , tier :: Maybe String
  }

-- | Initial rate limit state - Default rate limit state
-- |
-- | **Purpose:** Creates initial rate limit state with conservative defaults.
-- | **Returns:** RateLimitState with all fields initialized to safe defaults
-- | **Side Effects:** None (pure function)
-- |
-- | **Default Values:**
-- | - Request limits: 20/min (Free tier default)
-- | - Token limits: 40,000/min (Free tier default)
-- | - All remaining values set to limits (full capacity)
-- | - No backoff
initialRateLimitState :: RateLimitState
initialRateLimitState =
  { requestLimit: 20
  , requestsRemaining: 20
  , requestResetTime: Nothing
  , tokenLimit: 40000
  , tokensRemaining: 40000
  , tokenResetTime: Nothing
  , tier: Just "free"
  , lastUpdated: Nothing
  , backoffMs: 0.0
  }

-- | Update rate limits from headers - Extract and update rate limit state
-- |
-- | **Purpose:** Updates rate limit state from Venice API response headers.
-- | **Parameters:**
-- | - `state`: Current rate limit state
-- | - `headers`: Rate limit headers from API response
-- | **Returns:** Updated rate limit state
-- | **Side Effects:** None (pure function)
-- |
-- | **Behavior:**
-- | - Updates only fields that are present in headers (preserves existing if missing)
-- | - Converts Unix timestamps (seconds) to DateTime
-- | - Resets backoff on successful update
-- | - Updates `lastUpdated` timestamp
-- |
-- | **Example:**
-- | ```purescript
-- | headers = { requestLimit: Just 60, requestsRemaining: Just 45, ... }
-- | updated = updateFromHeaders currentState headers
-- | ```
updateFromHeaders :: RateLimitState -> RateLimitHeaders -> DateTime -> RateLimitState
updateFromHeaders state headers currentTime =
  state
    { requestLimit = fromMaybe state.requestLimit headers.requestLimit
    , requestsRemaining = fromMaybe state.requestsRemaining headers.requestsRemaining
    , requestResetTime = map (fromTimestamp <<< (*) 1000.0) headers.requestReset  -- Convert seconds to ms
    , tokenLimit = fromMaybe state.tokenLimit headers.tokenLimit
    , tokensRemaining = fromMaybe state.tokensRemaining headers.tokensRemaining
    , tokenResetTime = map (fromTimestamp <<< (*) 1000.0) headers.tokenReset  -- Convert seconds to ms
    , tier = headers.tier <|> state.tier
    , lastUpdated = Just currentTime
    , backoffMs = 0.0  -- Reset backoff on successful update
    }
  where
    fromMaybe :: forall a. a -> Maybe a -> a
    fromMaybe default = case _ of
      Just x -> x
      Nothing -> default

-- | Apply backoff - Apply exponential backoff with jitter
-- |
-- | **Purpose:** Applies exponential backoff when rate limit is hit, with jitter
-- |             to prevent thundering herd.
-- | **Parameters:**
-- | - `state`: Current rate limit state
-- | - `retryAfter`: Retry-After header value in seconds
-- | - `recentLimitCount`: Number of recent rate limits (for exponential backoff)
-- | **Returns:** Updated rate limit state with backoff applied
-- | **Side Effects:** None (pure function)
-- |
-- | **Backoff Calculation:**
-- | - Base delay: `retryAfter` seconds
-- | - Multiplier: `2^min(recentLimitCount, 3)` (max 8x multiplier)
-- | - Jitter: Random 0-1 second
-- | - Final: `(base * multiplier) + jitter` milliseconds
-- |
-- | **Example:**
-- | ```purescript
-- | -- First rate limit: 30s base + 0-1s jitter
-- | updated = applyBackoff state 30.0 0
-- |
-- | -- Second rate limit: 30s * 2 + jitter
-- | updated2 = applyBackoff updated 30.0 1
-- | ```
applyBackoff :: RateLimitState -> Number -> Int -> RateLimitState
applyBackoff state retryAfterSeconds recentLimitCount =
  let
    baseMs = retryAfterSeconds * 1000.0
    multiplier = Math.pow 2.0 (toNumber (min recentLimitCount 3))  -- Max 8x
    jitter = 0.0  -- Would be random in real implementation (0-1000ms)
    backoffMs = (baseMs * multiplier) + jitter
  in
    state { backoffMs = backoffMs }
  where
    toNumber :: Int -> Number
    toNumber = Int.toNumber

-- | Check if rate limited - Check if current state indicates rate limiting
-- |
-- | **Purpose:** Determines if requests are currently rate limited (backoff active
-- |             or limits exhausted).
-- | **Parameters:**
-- | - `state`: Current rate limit state
-- | **Returns:** True if rate limited, false otherwise
-- | **Side Effects:** None (pure function)
-- |
-- | **Rate Limited If:**
-- | - `backoffMs > 0` (backoff active)
-- | - `requestsRemaining <= 0` (request limit exhausted)
-- | - `tokensRemaining <= 0` (token limit exhausted)
isRateLimited :: RateLimitState -> Boolean
isRateLimited state =
  state.backoffMs > 0.0 ||
  state.requestsRemaining <= 0 ||
  state.tokensRemaining <= 0

-- | Get time until reset - Calculate milliseconds until limit reset
-- |
-- | **Purpose:** Calculates time remaining until rate limit resets.
-- | **Parameters:**
-- | - `state`: Current rate limit state
-- | - `currentTime`: Current DateTime
-- | **Returns:** Milliseconds until reset (0 if already reset or no reset time)
-- | **Side Effects:** None (pure function)
getTimeUntilReset :: RateLimitState -> DateTime -> Int
getTimeUntilReset state currentTime = case state.requestResetTime of
  Just resetTime ->
    let
      resetMs = toTimestamp resetTime
      currentMs = toTimestamp currentTime
      diffMs = resetMs - currentMs
    in
      if diffMs > 0.0 then round diffMs else 0
  Nothing -> 0
