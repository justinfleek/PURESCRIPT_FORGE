{-# LANGUAGE OverloadedStrings #-}

-- | Deep comprehensive unit tests for CircuitBreaker module
-- | Tests individual functions in isolation: createCircuitBreaker, recordSuccess,
-- | recordFailure, isAvailable, resetCircuitBreaker
module CircuitBreakerSpec where

import Test.Hspec
import Control.Concurrent.STM
import Control.Monad (replicateM, replicateM_)
import Data.Time (getCurrentTime, addUTCTime, diffUTCTime, secondsToDiffTime)
import Render.Gateway.STM.CircuitBreaker
  ( CircuitBreaker(..)
  , CircuitBreakerConfig(..)
  , CircuitState(..)
  , createCircuitBreaker
  , recordSuccess
  , recordFailure
  , isAvailable
  , resetCircuitBreaker
  )

-- | Deep comprehensive unit tests for CircuitBreaker module
spec :: Spec
spec = describe "CircuitBreaker Unit Tests" $ do
  describe "createCircuitBreaker" $ do
    it "creates circuit breaker with specified configuration" $ do
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 100
      cb <- atomically $ createCircuitBreaker now config
      
      -- Verify initial state
      state <- atomically $ readTVar (cbState cb)
      failures <- atomically $ readTVar (cbFailures cb)
      successes <- atomically $ readTVar (cbSuccesses cb)
      totalRequests <- atomically $ readTVar (cbTotalRequests cb)
      lastReset <- atomically $ readTVar (cbLastReset cb)
      
      state `shouldBe` CircuitClosed
      failures `shouldBe` 0
      successes `shouldBe` 0
      totalRequests `shouldBe` 0
      diffUTCTime lastReset now < 1.0 `shouldBe` True
      cbConfig cb `shouldBe` config

    it "BUG: creates circuit breaker with invalid failure threshold" $ do
      -- BUG: Failure threshold should be between 0.0 and 1.0, but createCircuitBreaker
      -- doesn't validate this. Values outside this range can cause incorrect behavior.
      now <- getCurrentTime
      
      -- Test with negative threshold
      let config1 = CircuitBreakerConfig (-0.1) 3 60 100
      cb1 <- atomically $ createCircuitBreaker now config1
      -- BUG: Negative threshold is stored, which is invalid
      cbcFailureThreshold (cbConfig cb1) `shouldBe` (-0.1)
      
      -- Test with threshold > 1.0
      let config2 = CircuitBreakerConfig 1.5 3 60 100
      cb2 <- atomically $ createCircuitBreaker now config2
      -- BUG: Threshold > 1.0 is stored, which means circuit will never open
      -- (failure rate can't exceed 1.0)
      cbcFailureThreshold (cbConfig cb2) `shouldBe` 1.5

    it "BUG: creates circuit breaker with zero success threshold" $ do
      -- BUG: Zero success threshold means circuit will never close from half-open
      -- state (needs 0 successes, but any failure will open it).
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 0 60 100
      cb <- atomically $ createCircuitBreaker now config
      
      -- BUG: Zero success threshold is stored, which means circuit will never
      -- transition from half-open to closed (needs 0 successes, but any failure
      -- opens it, so it will oscillate between half-open and open).
      cbcSuccessThreshold (cbConfig cb) `shouldBe` 0

    it "BUG: creates circuit breaker with zero timeout" $ do
      -- BUG: Zero timeout means circuit will immediately transition from open
      -- to half-open, potentially causing rapid oscillation.
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 0 100
      cb <- atomically $ createCircuitBreaker now config
      
      -- BUG: Zero timeout is stored, which means circuit will immediately
      -- transition from open to half-open, potentially causing rapid oscillation.
      cbcTimeoutSeconds (cbConfig cb) `shouldBe` 0

    it "BUG: creates circuit breaker with zero window size" $ do
      -- BUG: Zero window size means statistics reset immediately, making
      -- rolling window meaningless.
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 0
      cb <- atomically $ createCircuitBreaker now config
      
      -- BUG: Zero window size is stored, which means statistics reset
      -- immediately (elapsed >= 0 is always true), making rolling window
      -- meaningless.
      cbcWindowSize (cbConfig cb) `shouldBe` 0

  describe "recordSuccess" $ do
    it "records success and increments counters" $ do
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 100
      cb <- atomically $ createCircuitBreaker now config
      
      atomically $ recordSuccess cb now
      
      successes <- atomically $ readTVar (cbSuccesses cb)
      totalRequests <- atomically $ readTVar (cbTotalRequests cb)
      successes `shouldBe` 1
      totalRequests `shouldBe` 1

    it "transitions from half-open to closed when threshold met" $ do
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 100
      cb <- atomically $ createCircuitBreaker now config
      
      -- Set to half-open state
      atomically $ writeTVar (cbState cb) CircuitHalfOpen
      atomically $ writeTVar (cbSuccesses cb) 2
      
      -- Record success (should transition to closed)
      atomically $ recordSuccess cb now
      
      state <- atomically $ readTVar (cbState cb)
      successes <- atomically $ readTVar (cbSuccesses cb)
      state `shouldBe` CircuitClosed
      successes `shouldBe` 0  -- Reset on transition

    it "BUG: recordSuccess resets statistics when window expires" $ do
      -- BUG: recordSuccess (line 58-89) resets statistics when window expires
      -- (line 66-70). However, if window expires between recordSuccess calls,
      -- statistics are reset, potentially losing important failure information.
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 100
      cb <- atomically $ createCircuitBreaker now config
      
      -- Record some failures
      atomically $ recordFailure cb now
      atomically $ recordFailure cb now
      
      failures <- atomically $ readTVar (cbFailures cb)
      failures `shouldBe` 2
      
      -- Advance time beyond window size
      let later = addUTCTime (secondsToDiffTime 101) now
      atomically $ recordSuccess cb later
      
      failures <- atomically $ readTVar (cbFailures cb)
      -- BUG: Statistics are reset when window expires, so failures = 0
      -- This is correct for rolling window, but means failure history is lost.
      failures `shouldBe` 0

    it "BUG: recordSuccess may have race condition with window expiration" $ do
      -- BUG: recordSuccess (line 61-72) checks window expiration and resets
      -- statistics if expired. However, if multiple recordSuccess calls happen
      -- concurrently near the window boundary, they may all reset statistics,
      -- causing lost updates.
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 100
      cb <- atomically $ createCircuitBreaker now config
      
      -- Set lastReset to near window boundary
      let nearBoundary = addUTCTime (secondsToDiffTime 99) now
      atomically $ writeTVar (cbLastReset cb) nearBoundary
      atomically $ writeTVar (cbSuccesses cb) 5
      
      -- Advance time just past window boundary
      let pastBoundary = addUTCTime (secondsToDiffTime 2) nearBoundary
      atomically $ recordSuccess cb pastBoundary
      
      successes <- atomically $ readTVar (cbSuccesses cb)
      -- BUG: Window expired, so statistics reset, then success recorded
      -- Successes should be 1 (reset + 1), not 6 (5 + 1)
      successes `shouldBe` 1

    it "BUG: recordSuccess increments counters before checking state" $ do
      -- BUG: recordSuccess (line 74-76) increments successes and totalRequests
      -- before checking state (line 78). This means counters are incremented
      -- even if state transition fails or if state is already closed.
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 100
      cb <- atomically $ createCircuitBreaker now config
      
      -- Set to closed state with some existing counters
      atomically $ writeTVar (cbState cb) CircuitClosed
      atomically $ writeTVar (cbSuccesses cb) 10
      atomically $ writeTVar (cbTotalRequests cb) 20
      
      atomically $ recordSuccess cb now
      
      successes <- atomically $ readTVar (cbSuccesses cb)
      totalRequests <- atomically $ readTVar (cbTotalRequests cb)
      -- BUG: Counters are incremented even though state is already closed
      -- This is correct behavior, but means counters continue to grow even
      -- when circuit is closed and shouldn't need tracking.
      successes `shouldBe` 11
      totalRequests `shouldBe` 21

  describe "recordFailure" $ do
    it "records failure and increments counters" $ do
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 100
      cb <- atomically $ createCircuitBreaker now config
      
      atomically $ recordFailure cb now
      
      failures <- atomically $ readTVar (cbFailures cb)
      totalRequests <- atomically $ readTVar (cbTotalRequests cb)
      failures `shouldBe` 1
      totalRequests `shouldBe` 1

    it "opens circuit when failure threshold exceeded" $ do
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 100  -- 50% failure threshold
      cb <- atomically $ createCircuitBreaker now config
      
      -- Record failures to exceed threshold (2 failures out of 3 requests = 66% > 50%)
      atomically $ recordFailure cb now
      atomically $ recordFailure cb now
      atomically $ recordSuccess cb now  -- Total: 3 requests, 2 failures
      
      -- Next failure should open circuit
      let later = addUTCTime (secondsToDiffTime 1) now
      atomically $ recordFailure cb later
      
      state <- atomically $ readTVar (cbState cb)
      case state of
        CircuitOpen _ -> pure ()  -- Circuit opened
        _ -> expectationFailure "Circuit should be open"

    it "BUG: recordFailure may have division by zero" $ do
      -- BUG: recordFailure (line 117) calculates failure rate as:
      -- failureRate = fromIntegral failures / max 1.0 (fromIntegral total)
      -- The max 1.0 prevents division by zero, but if totalRequests is 0,
      -- failureRate = failures / 1.0 = failures, which is incorrect.
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 100
      cb <- atomically $ createCircuitBreaker now config
      
      -- Record failure with zero total requests (edge case test)
      -- Actually, recordFailure increments totalRequests first (line 110),
      -- so totalRequests will be 1, not 0. But if there's a bug where
      -- totalRequests is 0, the calculation would be wrong.
      atomically $ recordFailure cb now
      
      failures <- atomically $ readTVar (cbFailures cb)
      totalRequests <- atomically $ readTVar (cbTotalRequests cb)
      -- BUG: After first failure, totalRequests = 1, so failureRate = 1/1 = 1.0
      -- This exceeds threshold (0.5), so circuit should open.
      failures `shouldBe` 1
      totalRequests `shouldBe` 1
      
      state <- atomically $ readTVar (cbState cb)
      -- BUG: First failure with totalRequests = 1 gives failureRate = 1.0,
      -- which exceeds threshold (0.5), so circuit opens immediately.
      -- This may be too aggressive - circuit opens on first failure.
      case state of
        CircuitOpen _ -> pure ()  -- Circuit opened (may be too aggressive)
        _ -> expectationFailure "Circuit should be open after first failure"

    it "BUG: recordFailure resets statistics when window expires" $ do
      -- BUG: recordFailure (line 93-130) resets statistics when window expires
      -- (line 101-105). This is correct for rolling window, but means failure
      -- history is lost, potentially causing circuit to close prematurely.
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 100
      cb <- atomically $ createCircuitBreaker now config
      
      -- Record failures
      atomically $ recordFailure cb now
      atomically $ recordFailure cb now
      
      failures <- atomically $ readTVar (cbFailures cb)
      failures `shouldBe` 2
      
      -- Advance time beyond window size
      let later = addUTCTime (secondsToDiffTime 101) now
      atomically $ recordFailure cb later
      
      failures <- atomically $ readTVar (cbFailures cb)
      -- BUG: Statistics are reset when window expires, so failures = 1
      -- (reset + 1), not 3 (2 + 1). This means failure history is lost.
      failures `shouldBe` 1

    it "BUG: recordFailure opens circuit from half-open on any failure" $ do
      -- BUG: recordFailure (line 125-127) opens circuit from half-open state
      -- on any failure, regardless of success threshold. This is correct behavior,
      -- but means circuit will oscillate between half-open and open if failures
      -- are intermittent.
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 100
      cb <- atomically $ createCircuitBreaker now config
      
      -- Set to half-open state
      atomically $ writeTVar (cbState cb) CircuitHalfOpen
      atomically $ writeTVar (cbSuccesses cb) 2  -- 2 successes, need 3
      
      -- Record failure (should open circuit)
      atomically $ recordFailure cb now
      
      state <- atomically $ readTVar (cbState cb)
      -- BUG: Any failure in half-open state opens circuit, even if we had
      -- 2 successes and only needed 1 more. This is correct but aggressive.
      case state of
        CircuitOpen _ -> pure ()  -- Circuit opened
        _ -> expectationFailure "Circuit should be open"

  describe "isAvailable" $ do
    it "returns True when circuit is closed" $ do
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 100
      cb <- atomically $ createCircuitBreaker now config
      
      available <- atomically $ isAvailable cb now
      available `shouldBe` True

    it "returns True when circuit is half-open" $ do
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 100
      cb <- atomically $ createCircuitBreaker now config
      
      atomically $ writeTVar (cbState cb) CircuitHalfOpen
      available <- atomically $ isAvailable cb now
      available `shouldBe` True

    it "returns False when circuit is open and timeout not expired" $ do
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 100  -- 60 second timeout
      cb <- atomically $ createCircuitBreaker now config
      
      -- Open circuit
      atomically $ writeTVar (cbState cb) (CircuitOpen now)
      
      -- Check availability immediately (timeout not expired)
      available <- atomically $ isAvailable cb now
      available `shouldBe` False

    it "transitions from open to half-open when timeout expires" $ do
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 100  -- 60 second timeout
      cb <- atomically $ createCircuitBreaker now config
      
      -- Open circuit
      atomically $ writeTVar (cbState cb) (CircuitOpen now)
      
      -- Advance time past timeout
      let later = addUTCTime (secondsToDiffTime 61) now
      available <- atomically $ isAvailable cb later
      
      -- BUG: isAvailable (line 132-145) transitions from open to half-open
      -- when timeout expires (line 140-143). However, this transition happens
      -- during isAvailable check, which means the first request after timeout
      -- is allowed through (half-open state).
      available `shouldBe` True
      
      state <- atomically $ readTVar (cbState cb)
      state `shouldBe` CircuitHalfOpen

    it "BUG: isAvailable may have race condition with timeout expiration" $ do
      -- BUG: isAvailable (line 138-145) checks elapsed time and transitions
      -- from open to half-open if timeout expired. However, if multiple
      -- isAvailable calls happen concurrently near the timeout boundary,
      -- they may all transition to half-open, causing race conditions.
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 100
      cb <- atomically $ createCircuitBreaker now config
      
      -- Open circuit just before timeout
      let nearTimeout = addUTCTime (secondsToDiffTime 59) now
      atomically $ writeTVar (cbState cb) (CircuitOpen nearTimeout)
      
      -- Check availability just past timeout
      let pastTimeout = addUTCTime (secondsToDiffTime 2) nearTimeout
      available <- atomically $ isAvailable cb pastTimeout
      
      -- BUG: Timeout expired, so circuit transitions to half-open
      -- Multiple concurrent calls may all transition, causing race conditions.
      available `shouldBe` True

    it "BUG: isAvailable resets successes when transitioning to half-open" $ do
      -- BUG: isAvailable (line 142) resets successes when transitioning to
      -- half-open. This is correct, but means any successes accumulated before
      -- timeout are lost.
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 100
      cb <- atomically $ createCircuitBreaker now config
      
      -- Open circuit
      atomically $ writeTVar (cbState cb) (CircuitOpen now)
      -- Set some successes (edge case test)
      atomically $ writeTVar (cbSuccesses cb) 5
      
      -- Advance time past timeout
      let later = addUTCTime (secondsToDiffTime 61) now
      atomically $ isAvailable cb later
      
      successes <- atomically $ readTVar (cbSuccesses cb)
      -- BUG: Successes are reset when transitioning to half-open
      -- This is correct, but means any successes are lost.
      successes `shouldBe` 0

  describe "resetCircuitBreaker" $ do
    it "resets circuit breaker to closed state" $ do
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 100
      cb <- atomically $ createCircuitBreaker now config
      
      -- Set to open state with some statistics
      atomically $ writeTVar (cbState cb) (CircuitOpen now)
      atomically $ writeTVar (cbFailures cb) 10
      atomically $ writeTVar (cbSuccesses cb) 5
      atomically $ writeTVar (cbTotalRequests cb) 15
      
      -- Reset circuit breaker
      let later = addUTCTime (secondsToDiffTime 1) now
      atomically $ resetCircuitBreaker cb later
      
      state <- atomically $ readTVar (cbState cb)
      failures <- atomically $ readTVar (cbFailures cb)
      successes <- atomically $ readTVar (cbSuccesses cb)
      totalRequests <- atomically $ readTVar (cbTotalRequests cb)
      lastReset <- atomically $ readTVar (cbLastReset cb)
      
      state `shouldBe` CircuitClosed
      failures `shouldBe` 0
      successes `shouldBe` 0
      totalRequests `shouldBe` 0
      diffUTCTime lastReset later < 1.0 `shouldBe` True

    it "BUG: resetCircuitBreaker doesn't validate state before reset" $ do
      -- BUG: resetCircuitBreaker (line 148-154) resets circuit breaker without
      -- validating current state. This is correct, but means reset can be called
      -- even when circuit is already closed, potentially losing statistics.
      now <- getCurrentTime
      let config = CircuitBreakerConfig 0.5 3 60 100
      cb <- atomically $ createCircuitBreaker now config
      
      -- Set some statistics
      atomically $ writeTVar (cbFailures cb) 5
      atomically $ writeTVar (cbSuccesses cb) 10
      atomically $ writeTVar (cbTotalRequests cb) 15
      
      -- Reset (circuit is already closed)
      atomically $ resetCircuitBreaker cb now
      
      failures <- atomically $ readTVar (cbFailures cb)
      -- BUG: Statistics are reset even though circuit is already closed
      -- This may be intentional (manual reset), but loses statistics.
      failures `shouldBe` 0
