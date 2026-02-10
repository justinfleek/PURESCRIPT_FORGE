{-# LANGUAGE StrictData #-}
{-# LANGUAGE RecordWildCards #-}

-- | Bridge Error Circuit Breaker
-- |
-- | Circuit breaker pattern implementation for protecting
-- | downstream service calls. Tracks failure rates and
-- | automatically opens the circuit when thresholds are exceeded.
-- |
-- | State transitions:
-- |   Closed -> Open (failure rate exceeds threshold)
-- |   Open -> HalfOpen (timeout elapsed)
-- |   HalfOpen -> Closed (success threshold met)
-- |   HalfOpen -> Open (any failure)
-- |
-- | Dependencies:
-- | - Control.Concurrent.STM: Concurrent state management
-- | - Data.Time: Timeout calculations
-- | - Data.Int: Int32 for counters
module Bridge.Error.CircuitBreaker where

import Control.Concurrent.STM
  ( TVar
  , STM
  , newTVar
  , readTVar
  , writeTVar
  , modifyTVar'
  , atomically
  )
import Data.Int (Int32)
import Data.Time (UTCTime, diffUTCTime)

-- | Circuit breaker state
data CircuitState
  = Closed
  | HalfOpen
  | Open UTCTime -- timestamp when circuit was opened
  deriving (Eq, Show)

-- | Circuit breaker configuration
data CircuitBreakerConfig = CircuitBreakerConfig
  { cbcFailureThreshold :: Double -- failure rate threshold (0.0-1.0)
  , cbcSuccessThreshold :: Int32 -- successes needed to close from half-open
  , cbcTimeoutSeconds :: Int32 -- seconds before half-open attempt
  , cbcWindowSize :: Int32 -- rolling window size for rate calculation
  }
  deriving (Eq, Show)

-- | Circuit breaker state container
data CircuitBreaker = CircuitBreaker
  { cbState :: TVar CircuitState
  , cbFailures :: TVar Int32
  , cbSuccesses :: TVar Int32
  , cbTotalRequests :: TVar Int32
  , cbLastReset :: TVar UTCTime
  , cbConfig :: CircuitBreakerConfig
  }

-- | Circuit breaker status (snapshot for reporting)
data CircuitBreakerStatus = CircuitBreakerStatus
  { cbsState :: CircuitState
  , cbsFailures :: Int32
  , cbsSuccesses :: Int32
  , cbsTotalRequests :: Int32
  , cbsFailureRate :: Double
  }
  deriving (Eq, Show)

-- | Default circuit breaker configuration
-- |
-- | - 50% failure rate threshold
-- | - 3 successes to close from half-open
-- | - 30 second timeout before half-open
-- | - 100 request rolling window
defaultCircuitBreakerConfig :: CircuitBreakerConfig
defaultCircuitBreakerConfig = CircuitBreakerConfig
  { cbcFailureThreshold = 0.5
  , cbcSuccessThreshold = 3
  , cbcTimeoutSeconds = 30
  , cbcWindowSize = 100
  }

-- | Create a new circuit breaker
-- |
-- | Starts in Closed state with all counters at zero.
-- | The initial time is used for the lastReset timestamp.
createCircuitBreaker :: UTCTime -> CircuitBreakerConfig -> STM CircuitBreaker
createCircuitBreaker initialTime config = do
  state <- newTVar Closed
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

-- | Record a successful request
-- |
-- | In HalfOpen state, increments success counter and
-- | transitions to Closed if the success threshold is met.
recordSuccess :: CircuitBreaker -> STM ()
recordSuccess CircuitBreaker {..} = do
  currentState <- readTVar cbState
  modifyTVar' cbSuccesses (+ 1)
  modifyTVar' cbTotalRequests (+ 1)

  case currentState of
    HalfOpen -> do
      successes <- readTVar cbSuccesses
      if successes >= cbcSuccessThreshold cbConfig
        then do
          writeTVar cbState Closed
          writeTVar cbFailures 0
          writeTVar cbSuccesses 0
        else
          pure ()
    _ -> pure ()

-- | Record a failed request
-- |
-- | In Closed state, calculates failure rate and opens the
-- | circuit if the threshold is exceeded.
-- | In HalfOpen state, immediately reopens the circuit.
recordFailure :: CircuitBreaker -> UTCTime -> STM ()
recordFailure CircuitBreaker {..} now = do
  modifyTVar' cbFailures (+ 1)
  modifyTVar' cbTotalRequests (+ 1)

  currentState <- readTVar cbState
  case currentState of
    Closed -> do
      failures <- readTVar cbFailures
      total <- readTVar cbTotalRequests
      let failureRate = fromIntegral failures / max 1.0 (fromIntegral total)

      if failureRate >= cbcFailureThreshold cbConfig
        then do
          writeTVar cbState (Open now)
          writeTVar cbLastReset now
        else
          pure ()

    HalfOpen -> do
      writeTVar cbState (Open now)
      writeTVar cbLastReset now

    Open _ -> pure ()

-- | Check if the circuit breaker allows requests
-- |
-- | Returns True for Closed and HalfOpen states.
-- | For Open state, checks if the timeout has elapsed
-- | and transitions to HalfOpen if so.
isAvailable :: CircuitBreaker -> UTCTime -> STM Bool
isAvailable CircuitBreaker {..} now = do
  currentState <- readTVar cbState
  case currentState of
    Closed -> pure True
    HalfOpen -> pure True
    Open openedAt -> do
      let elapsed = realToFrac (diffUTCTime now openedAt) :: Double
      if elapsed >= fromIntegral (cbcTimeoutSeconds cbConfig)
        then do
          writeTVar cbState HalfOpen
          writeTVar cbSuccesses 0
          pure True
        else
          pure False

-- | Reset the circuit breaker to Closed state
-- |
-- | Clears all counters and resets the state.
resetCircuitBreaker :: CircuitBreaker -> UTCTime -> STM ()
resetCircuitBreaker CircuitBreaker {..} now = do
  writeTVar cbState Closed
  writeTVar cbFailures 0
  writeTVar cbSuccesses 0
  writeTVar cbTotalRequests 0
  writeTVar cbLastReset now

-- | Get current circuit breaker status
-- |
-- | Returns a snapshot of the current state and counters
-- | for monitoring and reporting.
getStatus :: CircuitBreaker -> STM CircuitBreakerStatus
getStatus CircuitBreaker {..} = do
  state <- readTVar cbState
  failures <- readTVar cbFailures
  successes <- readTVar cbSuccesses
  total <- readTVar cbTotalRequests
  let failureRate = if total > 0
        then fromIntegral failures / fromIntegral total
        else 0.0
  pure CircuitBreakerStatus
    { cbsState = state
    , cbsFailures = failures
    , cbsSuccesses = successes
    , cbsTotalRequests = total
    , cbsFailureRate = failureRate
    }
