{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}

-- | Bridge Circuit Breaker - Circuit Breaker Pattern for External Services
-- |
-- | **What:** Implements circuit breaker pattern for external service calls (Venice API,
-- |         PostgreSQL, Lean LSP). Prevents cascading failures by opening circuit when
-- |         failure rate exceeds threshold.
-- | **Why:** Protects system from external service failures. Prevents overwhelming
-- |         failing services with requests. Enables graceful degradation.
-- | **How:** Tracks success/failure rates in rolling window. Opens circuit when failure
-- |         rate exceeds threshold. Half-open state allows test requests. Closes when
-- |         service recovers.
-- |
-- | **Dependencies:**
-- | - `Control.Concurrent.STM`: Thread-safe state management
-- | - `Data.Time`: Time-based state transitions
-- |
-- | **Mathematical Foundation:**
-- | - **Failure Rate:** `failures / totalRequests` in rolling window
-- | - **State Transitions:**
-- |   - Closed → Open: `failureRate >= threshold`
-- |   - Open → HalfOpen: `elapsed >= timeoutSeconds`
-- |   - HalfOpen → Closed: `successes >= successThreshold`
-- |   - HalfOpen → Open: Any failure
-- |
-- | **Usage Example:**
-- | ```haskell
-- | import Bridge.Error.CircuitBreaker as CB
-- |
-- | -- Create circuit breaker
-- | breaker <- atomically $ CB.createCircuitBreaker config
-- |
-- | -- Check if available
-- | available <- atomically $ CB.isAvailable breaker now
-- | if available then
-- |   -- Make request
-- |   result <- callVeniceAPI
-- |   case result of
-- |     Right _ -> atomically $ CB.recordSuccess breaker
-- |     Left _ -> atomically $ CB.recordFailure breaker now
-- | else
-- |   -- Circuit open, use fallback
-- | ```
module Bridge.Error.CircuitBreaker where

module Bridge.Error.CircuitBreaker where

import Prelude hiding (head, tail)
import Control.Concurrent.STM
import Control.Monad.IO.Class (liftIO)
import Data.Int (Int32)
import Data.Time (UTCTime, diffUTCTime, getCurrentTime)

-- | Circuit breaker state
data CircuitState
  = CircuitClosed
  | CircuitHalfOpen
  | CircuitOpen UTCTime -- timestamp when opened
  deriving (Eq, Show)

-- | Circuit breaker configuration
data CircuitBreakerConfig = CircuitBreakerConfig
  { cbcFailureThreshold :: Double -- failure rate threshold (0.0-1.0), default: 0.5
  , cbcSuccessThreshold :: Int32 -- successes needed to close from half-open, default: 5
  , cbcTimeoutSeconds :: Int32 -- time before half-open attempt, default: 60
  , cbcWindowSize :: Int32 -- rolling window size, default: 100
  }
  deriving (Eq, Show)

-- | Default circuit breaker configuration
defaultCircuitBreakerConfig :: CircuitBreakerConfig
defaultCircuitBreakerConfig = CircuitBreakerConfig
  { cbcFailureThreshold = 0.5
  , cbcSuccessThreshold = 5
  , cbcTimeoutSeconds = 60
  , cbcWindowSize = 100
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
  deriving (Eq)

-- | Create circuit breaker
-- |
-- | **Purpose:** Creates a new circuit breaker with given configuration.
-- | **Parameters:**
-- | - `config`: Circuit breaker configuration
-- | **Returns:** Circuit breaker instance (in STM)
createCircuitBreaker :: CircuitBreakerConfig -> IO CircuitBreaker
createCircuitBreaker config = do
  now <- getCurrentTime
  atomically $ do
    state <- newTVar CircuitClosed
    failures <- newTVar 0
    successes <- newTVar 0
    totalRequests <- newTVar 0
    lastReset <- newTVar now
    pure CircuitBreaker
      { cbState = state
      , cbFailures = failures
      , cbSuccesses = successes
      , cbTotalRequests = totalRequests
      , cbLastReset = lastReset
      , cbConfig = config
      }

-- | Record success
-- |
-- | **Purpose:** Records a successful request. Updates circuit breaker state.
-- | **Parameters:**
-- | - `breaker`: Circuit breaker instance
-- | **Side Effects:** Updates success count, may transition state
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
-- |
-- | **Purpose:** Records a failed request. May open circuit if failure rate too high.
-- | **Parameters:**
-- | - `breaker`: Circuit breaker instance
-- | - `now`: Current time
-- | **Side Effects:** Updates failure count, may transition state
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
-- |
-- | **Purpose:** Determines if circuit breaker allows request based on current state.
-- | **Parameters:**
-- | - `breaker`: Circuit breaker instance
-- | - `now`: Current time
-- | **Returns:** True if request allowed, false if circuit open
-- |
-- | **Logic:**
-- | - Closed: Always allow
-- | - HalfOpen: Allow (test request)
-- | - Open: Allow only if timeout elapsed (transition to HalfOpen)
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
-- |
-- | **Purpose:** Manually resets circuit breaker to closed state (admin operation).
-- | **Parameters:**
-- | - `breaker`: Circuit breaker instance
-- | - `now`: Current time
-- | **Side Effects:** Resets all counters and state
resetCircuitBreaker :: CircuitBreaker -> UTCTime -> STM ()
resetCircuitBreaker CircuitBreaker {..} now = do
  writeTVar cbState CircuitClosed
  writeTVar cbFailures 0
  writeTVar cbSuccesses 0
  writeTVar cbTotalRequests 0
  writeTVar cbLastReset now

-- | Get circuit breaker status
-- |
-- | **Purpose:** Returns current circuit breaker status for monitoring.
-- | **Parameters:**
-- | - `breaker`: Circuit breaker instance
-- | **Returns:** Status information
getStatus :: CircuitBreaker -> STM CircuitBreakerStatus
getStatus CircuitBreaker {..} = do
  state <- readTVar cbState
  failures <- readTVar cbFailures
  successes <- readTVar cbSuccesses
  total <- readTVar cbTotalRequests
  lastReset <- readTVar cbLastReset
  
  let failureRate = if total > 0 then fromIntegral failures / fromIntegral total else 0.0
  
  pure CircuitBreakerStatus
    { cbsState = state
    , cbsFailures = failures
    , cbsSuccesses = successes
    , cbsTotalRequests = total
    , cbsFailureRate = failureRate
    , cbsLastReset = lastReset
    }

-- | Circuit breaker status
data CircuitBreakerStatus = CircuitBreakerStatus
  { cbsState :: CircuitState
  , cbsFailures :: Int32
  , cbsSuccesses :: Int32
  , cbsTotalRequests :: Int32
  , cbsFailureRate :: Double
  , cbsLastReset :: UTCTime
  }
  deriving (Eq, Show)
