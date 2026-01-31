{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}

-- | Render Gateway Rate Limiter
-- | Token bucket rate limiter with STM atomicity
module Render.Gateway.STM.RateLimiter where

import Prelude hiding (head, tail)
import Control.Concurrent.STM
import Control.Monad (unless)
import Data.Int (Int32)
import Data.Time (UTCTime, diffUTCTime)
import Render.Gateway.STM.Clock (Clock, readClockSTM)

-- | Rate limiter state
data RateLimiter = RateLimiter
  { rlTokens :: TVar Double
  , rlLastRefill :: TVar UTCTime
  , rlCapacity :: Double
  , rlRefillRate :: Double -- tokens per second
  }

-- | Create rate limiter
createRateLimiter :: Double -> Double -> UTCTime -> STM RateLimiter
createRateLimiter capacity refillRate now = do
  tokens <- newTVar capacity
  lastRefill <- newTVar now
  pure RateLimiter
    { rlTokens = tokens
    , rlLastRefill = lastRefill
    , rlCapacity = capacity
    , rlRefillRate = refillRate
    }

-- | Refill tokens based on elapsed time
refillTokens :: RateLimiter -> UTCTime -> STM ()
refillTokens RateLimiter {..} now = do
  lastTime <- readTVar rlLastRefill
  let elapsed = realToFrac (diffUTCTime now lastTime)
  let tokensToAdd = elapsed * rlRefillRate
  
  currentTokens <- readTVar rlTokens
  let newTokens = min rlCapacity (currentTokens + tokensToAdd)
  
  writeTVar rlTokens newTokens
  writeTVar rlLastRefill now

-- | Try to acquire token (non-blocking)
acquireToken :: RateLimiter -> UTCTime -> STM Bool
acquireToken rl now = do
  refillTokens rl now
  tokens <- readTVar (rlTokens rl)
  if tokens >= 1.0 then do
    modifyTVar' (rlTokens rl) (\t -> t - 1.0)
    pure True
  else
    pure False

-- | Acquire token with blocking retry (uses clock TVar pattern)
acquireTokenBlocking :: RateLimiter -> Clock -> STM ()
acquireTokenBlocking rl clock = do
  (_, now) <- readClockSTM clock
  acquired <- acquireToken rl now
  unless acquired retry

-- | Get current token count
getTokenCount :: RateLimiter -> UTCTime -> STM Double
getTokenCount rl now = do
  refillTokens rl now
  readTVar (rlTokens rl)
