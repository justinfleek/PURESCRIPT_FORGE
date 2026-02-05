{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}

-- | Render Gateway Circuit Breaker
-- | Per-backend circuit breaker with rolling window statistics
module Render.Gateway.STM.CircuitBreaker where

import Prelude hiding (head, tail)
import Control.Concurrent.STM
import Data.Int (Int32)
import Data.Time (UTCTime, diffUTCTime)

-- | Circuit breaker state
data CircuitState
  = CircuitClosed
  | CircuitHalfOpen
  | CircuitOpen UTCTime -- timestamp when opened
  deriving (Eq, Show)

-- | Circuit breaker configuration
data CircuitBreakerConfig = CircuitBreakerConfig
  { cbcFailureThreshold :: Double -- failure rate threshold (0.0-1.0)
  , cbcSuccessThreshold :: Int32 -- successes needed to close from half-open
  , cbcTimeoutSeconds :: Int32 -- time before half-open attempt
  , cbcWindowSize :: Int32 -- rolling window size
  }

-- | Circuit breaker state
data CircuitBreaker = CircuitBreaker
  { cbState :: TVar CircuitState
  , cbFailures :: TVar Int32
  , cbSuccesses :: TVar Int32
  , cbTotalRequests :: TVar Int32
  , cbLastReset :: TVar UTCTime
  , cbConfig :: CircuitBreakerConfig
  }

-- | Create circuit breaker
-- | Note: lastReset must be initialized with clock time before use
createCircuitBreaker :: UTCTime -> CircuitBreakerConfig -> STM CircuitBreaker
createCircuitBreaker initialTime config = do
  state <- newTVar CircuitClosed
  failures <- newTVar 0
  successes <- newTVar 0
  totalRequests <- newTVar 0
  lastReset <- newTVar initialTime
  pure CircuitBreaker
    { cbState = state
    , cbFailures = failures
    , cbSuccesses = successes
    , cbTotalRequests = totalRequests
    , cbLastReset = lastReset
    , cbConfig = config
    }

-- | Record success
recordSuccess :: CircuitBreaker -> STM ()
recordSuccess CircuitBreaker {..} = do
  currentState <- readTVar cbState
  modifyTVar' cbSuccesses (+ 1)
  modifyTVar' cbTotalRequests (+ 1)
  
  case currentState of
    CircuitHalfOpen -> do
      successes <- readTVar cbSuccesses
      if successes >= cbcSuccessThreshold cbConfig then do
        writeTVar cbState CircuitClosed
        writeTVar cbFailures 0
        writeTVar cbSuccesses 0
      else
        pure ()
    _ -> pure ()

-- | Record failure
recordFailure :: CircuitBreaker -> UTCTime -> STM ()
recordFailure CircuitBreaker {..} now = do
  modifyTVar' cbFailures (+ 1)
  modifyTVar' cbTotalRequests (+ 1)
  
  currentState <- readTVar cbState
  case currentState of
    CircuitClosed -> do
      failures <- readTVar cbFailures
      total <- readTVar cbTotalRequests
      let failureRate = fromIntegral failures / max 1.0 (fromIntegral total)
      
      if failureRate >= cbcFailureThreshold cbConfig then do
        writeTVar cbState (CircuitOpen now)
        writeTVar cbLastReset now
      else
        pure ()
    
    CircuitHalfOpen -> do
      writeTVar cbState (CircuitOpen now)
      writeTVar cbLastReset now
    
    CircuitOpen _ -> pure ()

-- | Check if circuit breaker allows request
isAvailable :: CircuitBreaker -> UTCTime -> STM Bool
isAvailable CircuitBreaker {..} now = do
  currentState <- readTVar cbState
  case currentState of
    CircuitClosed -> pure True
    CircuitHalfOpen -> pure True
    CircuitOpen openedAt -> do
      let elapsed = realToFrac (diffUTCTime now openedAt)
      if elapsed >= fromIntegral (cbcTimeoutSeconds cbConfig) then do
        writeTVar cbState CircuitHalfOpen
        writeTVar cbSuccesses 0
        pure True
      else
        pure False

-- | Reset circuit breaker
resetCircuitBreaker :: CircuitBreaker -> UTCTime -> STM ()
resetCircuitBreaker CircuitBreaker {..} now = do
  writeTVar cbState CircuitClosed
  writeTVar cbFailures 0
  writeTVar cbSuccesses 0
  writeTVar cbTotalRequests 0
  writeTVar cbLastReset now
