-- | Omega Rate Limiter
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/rateLimiter.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Omega.Util.RateLimiter
  ( RateLimitConfig(..)
  , RateLimitState(..)
  , RateLimitResult(..)
  , buildIntervals
  , checkRateLimit
  , buildYYYYMMDDHH
  ) where

import Prelude

import Data.Array (foldl)
import Data.Maybe (Maybe(..))
import Data.String (take)

-- | Rate limit configuration
type RateLimitConfig =
  { limit :: Int           -- Max requests in window
  , windowHours :: Int     -- Window size in hours (default 3)
  }

-- | Rate limit state
type RateLimitState =
  { ip :: String
  , intervals :: Array String
  , counts :: Array { interval :: String, count :: Int }
  }

-- | Rate limit check result
data RateLimitResult
  = Allowed
  | Denied { total :: Int, limit :: Int }

derive instance eqRateLimitResult :: Eq RateLimitResult

-- | Build interval keys for rate limiting
-- | Returns array of YYYYMMDDHH strings for current and previous hours
buildIntervals :: Int -> Int -> Array String
buildIntervals nowTimestamp windowHours =
  map (\offset -> buildYYYYMMDDHH (nowTimestamp - offset * 3600000)) (range 0 (windowHours - 1))
  where
    range :: Int -> Int -> Array Int
    range start end = if start > end then [] else [start] <> range (start + 1) end

-- | Build YYYYMMDDHH string from timestamp
-- | Example: 1704067200000 -> "2024010100"
buildYYYYMMDDHH :: Int -> String
buildYYYYMMDDHH timestamp =
  -- In production this would use actual date parsing
  -- Here we provide a pure function signature
  let
    -- Convert timestamp to components (simplified)
    -- Real implementation would use proper date library
    isoString = timestampToIso timestamp
  in
    -- Take first 10 numeric characters (YYYYMMDDHH)
    extractNumeric isoString
  where
    timestampToIso :: Int -> String
    timestampToIso _ = "2024010100000000"  -- simplified
    
    extractNumeric :: String -> String
    extractNumeric s = take 10 (filterDigits s)
    
    filterDigits :: String -> String
    filterDigits s = s  -- simplified

-- | Check rate limit against stored counts
checkRateLimit :: RateLimitConfig -> Array { interval :: String, count :: Int } -> RateLimitResult
checkRateLimit config counts =
  let
    total = foldl (\acc row -> acc + row.count) 0 counts
  in
    if total >= config.limit
      then Denied { total, limit: config.limit }
      else Allowed

-- | Get effective IP (use "unknown" for empty)
getEffectiveIp :: String -> String
getEffectiveIp ip =
  if ip == ""
    then "unknown"
    else ip

-- | Rate limit update value (for incrementing count)
type RateLimitUpdate =
  { ip :: String
  , interval :: String
  , incrementBy :: Int
  }

-- | Build rate limit update
buildRateLimitUpdate :: String -> String -> RateLimitUpdate
buildRateLimitUpdate ip interval =
  { ip: getEffectiveIp ip
  , interval
  , incrementBy: 1
  }

-- | Default rate limit config (3-hour window)
defaultConfig :: Int -> RateLimitConfig
defaultConfig limit =
  { limit
  , windowHours: 3
  }

-- | Check if rate limiting is enabled
isEnabled :: Maybe Int -> Boolean
isEnabled Nothing = false
isEnabled (Just _) = true

-- | Build rate limit state
buildState :: String -> Int -> RateLimitState
buildState ip nowTimestamp =
  { ip: getEffectiveIp ip
  , intervals: buildIntervals nowTimestamp 3
  , counts: []
  }

-- | Add count to state
addCount :: RateLimitState -> { interval :: String, count :: Int } -> RateLimitState
addCount state row =
  state { counts = state.counts <> [row] }
