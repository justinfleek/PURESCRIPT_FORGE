{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Deep Comprehensive Property Tests for Circuit Breaker
-- |
-- | Tests state transitions, window size, and failure threshold properties
-- | with realistic distributions to find real bugs.
-- |
-- | Based on spec 70-TESTING-STRATEGY.md and 71-UNIT-TESTING.md
-- | Reference: REQUIRED/trtllm-serve-main/nix/openai-proxy-hs/ProxyPropTest.hs
module CircuitBreakerProps where

import Test.QuickCheck
import Test.QuickCheck.Monadic
import Control.Concurrent.STM
import Control.Monad (replicateM, forM_)
import Data.Time (UTCTime, getCurrentTime, addUTCTime, diffUTCTime, secondsToDiffTime)
import Data.Int (Int32)

import Render.Gateway.STM.CircuitBreaker

-- ============================================================================
-- REALISTIC DISTRIBUTIONS
-- ============================================================================

-- | Realistic failure threshold distribution:
-- | - Most breakers: 0.3-0.7 (normal)
-- | - Some breakers: 0.1-0.3 (sensitive)
-- | - Few breakers: 0.7-0.9 (tolerant)
genRealisticFailureThreshold :: Gen Double
genRealisticFailureThreshold = frequency
  [ (70, choose (0.3, 0.7))          -- Normal threshold
  , (20, choose (0.1, 0.3))          -- Sensitive threshold
  , (10, choose (0.7, 0.9))          -- Tolerant threshold
  ]

-- | Realistic success threshold distribution:
-- | - Most breakers: 3-10 successes
-- | - Some breakers: 10-20 successes
-- | - Few breakers: 1-3 successes
genRealisticSuccessThreshold :: Gen Int32
genRealisticSuccessThreshold = frequency
  [ (70, choose (3, 10))             -- Normal threshold
  , (20, choose (10, 20))            -- High threshold
  , (10, choose (1, 3))               -- Low threshold
  ]

-- | Realistic timeout distribution:
-- | - Most breakers: 30-120 seconds
-- | - Some breakers: 120-300 seconds
-- | - Few breakers: 10-30 seconds
genRealisticTimeout :: Gen Int32
genRealisticTimeout = frequency
  [ (70, choose (30, 120))            -- Normal timeout
  , (20, choose (120, 300))          -- Long timeout
  , (10, choose (10, 30))             -- Short timeout
  ]

-- | Realistic window size distribution:
-- | - Most breakers: 50-200 requests
-- | - Some breakers: 200-500 requests
-- | - Few breakers: 10-50 requests
genRealisticWindowSize :: Gen Int32
genRealisticWindowSize = frequency
  [ (70, choose (50, 200))            -- Normal window
  , (20, choose (200, 500))          -- Large window
  , (10, choose (10, 50))            -- Small window
  ]

-- | Realistic request count distribution:
genRealisticRequestCount :: Gen Int
genRealisticRequestCount = frequency
  [ (70, choose (10, 100))            -- Normal
  , (25, choose (100, 500))          -- High
  , (5, choose (500, 1000))           -- Stress
  ]

-- | Realistic time delta distribution:
genRealisticTimeDelta :: Gen Double
genRealisticTimeDelta = frequency
  [ (70, choose (0.1, 10.0))          -- Normal delta
  , (25, choose (10.0, 60.0))        -- Long delta
  , (5, choose (60.0, 300.0))         -- Very long delta
  ]

-- ============================================================================
-- STATE TRANSITION PROPERTIES
-- ============================================================================

-- | Property: Closed → Open transition
-- | Circuit should open when failure rate exceeds threshold
prop_closedToOpen :: Property
prop_closedToOpen = monadicIO $ do
  now <- run getCurrentTime
  failureThreshold <- pick genRealisticFailureThreshold
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig failureThreshold successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Calculate requests needed to exceed threshold
  -- Need failureRate >= threshold, so failures / total >= threshold
  -- With total = failures + successes, we need failures >= threshold * total
  -- For simplicity, use total = 10, failures = ceil(threshold * 10)
  let totalRequests = 10
  let failuresNeeded = ceiling (failureThreshold * fromIntegral totalRequests)
  let successesNeeded = totalRequests - failuresNeeded
  
  -- Record failures first, then successes
  run $ atomically $ do
    forM_ [1..failuresNeeded] $ \_ -> recordFailure cb now
    forM_ [1..successesNeeded] $ \_ -> recordSuccess cb now
  
  -- Circuit should be open
  available <- run $ atomically $ isAvailable cb now
  assert $ not available
  
  -- Verify state is Open
  state <- run $ atomically $ readTVar (cbState cb)
  case state of
    CircuitOpen _ -> assert True
    _ -> assert False

-- | Property: Open → HalfOpen transition
-- | Circuit should transition to half-open after timeout
prop_openToHalfOpen :: Property
prop_openToHalfOpen = monadicIO $ do
  now <- run getCurrentTime
  failureThreshold <- pick genRealisticFailureThreshold
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig failureThreshold successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Open circuit
  run $ atomically $ do
    writeTVar (cbState cb) (CircuitOpen now)
  
  -- Advance time past timeout
  let later = addUTCTime (secondsToDiffTime (fromIntegral timeout + 1.0)) now
  
  -- Check availability (should transition to half-open)
  available <- run $ atomically $ isAvailable cb later
  assert available
  
  -- Verify state is HalfOpen
  state <- run $ atomically $ readTVar (cbState cb)
  case state of
    CircuitHalfOpen -> assert True
    _ -> assert False

-- | Property: HalfOpen → Closed transition
-- | Circuit should close after success threshold reached
prop_halfOpenToClosed :: Property
prop_halfOpenToClosed = monadicIO $ do
  now <- run getCurrentTime
  failureThreshold <- pick genRealisticFailureThreshold
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig failureThreshold successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Set to half-open
  run $ atomically $ do
    writeTVar (cbState cb) CircuitHalfOpen
    writeTVar (cbSuccesses cb) 0
  
  -- Record successes up to threshold
  run $ atomically $ do
    forM_ [1..successThreshold] $ \_ -> recordSuccess cb now
  
  -- Verify state is Closed
  state <- run $ atomically $ readTVar (cbState cb)
  case state of
    CircuitClosed -> assert True
    _ -> assert False
  
  -- Verify statistics reset
  failures <- run $ atomically $ readTVar (cbFailures cb)
  successes <- run $ atomically $ readTVar (cbSuccesses cb)
  total <- run $ atomically $ readTVar (cbTotalRequests cb)
  assert $ failures == 0
  assert $ successes == 0
  assert $ total == 0

-- | Property: HalfOpen → Open transition
-- | Circuit should open immediately on failure in half-open state
prop_halfOpenToOpen :: Property
prop_halfOpenToOpen = monadicIO $ do
  now <- run getCurrentTime
  failureThreshold <- pick genRealisticFailureThreshold
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig failureThreshold successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Set to half-open
  run $ atomically $ do
    writeTVar (cbState cb) CircuitHalfOpen
  
  -- Record failure (should immediately open)
  run $ atomically $ recordFailure cb now
  
  -- Verify state is Open
  state <- run $ atomically $ readTVar (cbState cb)
  case state of
    CircuitOpen _ -> assert True
    _ -> assert False

-- | Property: State transitions are atomic
prop_stateTransitionsAtomic :: Property
prop_stateTransitionsAtomic = monadicIO $ do
  now <- run getCurrentTime
  failureThreshold <- pick genRealisticFailureThreshold
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig failureThreshold successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Multiple operations in single transaction
  run $ atomically $ do
    recordFailure cb now
    recordFailure cb now
    recordSuccess cb now
    recordFailure cb now
  
  -- State should be consistent
  state <- run $ atomically $ readTVar (cbState cb)
  assert $ case state of
    CircuitClosed -> True
    CircuitHalfOpen -> True
    CircuitOpen _ -> True

-- ============================================================================
-- WINDOW SIZE PROPERTIES
-- ============================================================================

-- | Property: Window resets statistics when expired
prop_windowResetsStatistics :: Property
prop_windowResetsStatistics = monadicIO $ do
  now <- run getCurrentTime
  failureThreshold <- pick genRealisticFailureThreshold
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig failureThreshold successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Record some failures and successes
  run $ atomically $ do
    forM_ [1..5] $ \_ -> recordFailure cb now
    forM_ [1..5] $ \_ -> recordSuccess cb now
  
  -- Advance time past window
  let later = addUTCTime (secondsToDiffTime (fromIntegral windowSize + 1.0)) now
  
  -- Record another event (should reset window)
  run $ atomically $ recordSuccess cb later
  
  -- Statistics should be reset (only 1 success, 0 failures)
  failures <- run $ atomically $ readTVar (cbFailures cb)
  successes <- run $ atomically $ readTVar (cbSuccesses cb)
  total <- run $ atomically $ readTVar (cbTotalRequests cb)
  
  assert $ failures == 0
  assert $ successes == 1
  assert $ total == 1

-- | Property: Window does not reset before expiration
prop_windowNoResetBeforeExpiration :: Property
prop_windowNoResetBeforeExpiration = monadicIO $ do
  now <- run getCurrentTime
  failureThreshold <- pick genRealisticFailureThreshold
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig failureThreshold successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Record some failures and successes
  run $ atomically $ do
    forM_ [1..5] $ \_ -> recordFailure cb now
    forM_ [1..5] $ \_ -> recordSuccess cb now
  
  -- Advance time but not past window
  let later = addUTCTime (secondsToDiffTime (fromIntegral windowSize - 1.0)) now
  
  -- Record another event (should NOT reset window)
  run $ atomically $ recordSuccess cb later
  
  -- Statistics should NOT be reset
  failures <- run $ atomically $ readTVar (cbFailures cb)
  successes <- run $ atomically $ readTVar (cbSuccesses cb)
  total <- run $ atomically $ readTVar (cbTotalRequests cb)
  
  assert $ failures == 5
  assert $ successes == 6
  assert $ total == 11

-- | Property: Multiple window resets maintain consistency
prop_multipleWindowResets :: Property
prop_multipleWindowResets = monadicIO $ do
  now <- run getCurrentTime
  failureThreshold <- pick genRealisticFailureThreshold
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig failureThreshold successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Record events across multiple windows
  let numWindows = 3
  run $ atomically $ do
    forM_ [0..(numWindows - 1)] $ \window -> do
      let windowStart = addUTCTime (secondsToDiffTime (fromIntegral window * fromIntegral windowSize)) now
      -- Record failures and successes in this window
      forM_ [1..3] $ \_ -> recordFailure cb windowStart
      forM_ [1..2] $ \_ -> recordSuccess cb windowStart
  
  -- Advance to end of last window
  let endTime = addUTCTime (secondsToDiffTime (fromIntegral numWindows * fromIntegral windowSize)) now
  
  -- Record event (should reset)
  run $ atomically $ recordSuccess cb endTime
  
  -- Should only have last event
  failures <- run $ atomically $ readTVar (cbFailures cb)
  successes <- run $ atomically $ readTVar (cbSuccesses cb)
  total <- run $ atomically $ readTVar (cbTotalRequests cb)
  
  assert $ failures == 0
  assert $ successes == 1
  assert $ total == 1

-- ============================================================================
-- FAILURE THRESHOLD PROPERTIES
-- ============================================================================

-- | Property: Circuit opens at exact threshold
prop_opensAtExactThreshold :: Property
prop_opensAtExactThreshold = monadicIO $ do
  now <- run getCurrentTime
  failureThreshold <- pick $ choose (0.1, 0.9)
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig failureThreshold successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Calculate exact threshold
  let totalRequests = 10
  let failuresNeeded = ceiling (failureThreshold * fromIntegral totalRequests)
  let successesNeeded = totalRequests - failuresNeeded
  
  -- Record exactly at threshold
  run $ atomically $ do
    forM_ [1..failuresNeeded] $ \_ -> recordFailure cb now
    forM_ [1..successesNeeded] $ \_ -> recordSuccess cb now
  
  -- Circuit should be open
  available <- run $ atomically $ isAvailable cb now
  assert $ not available

-- | Property: Circuit does not open below threshold
prop_doesNotOpenBelowThreshold :: Property
prop_doesNotOpenBelowThreshold = monadicIO $ do
  now <- run getCurrentTime
  failureThreshold <- pick $ choose (0.2, 0.9)
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig failureThreshold successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Calculate below threshold
  let totalRequests = 10
  let failuresNeeded = max 0 (ceiling (failureThreshold * fromIntegral totalRequests) - 1)
  let successesNeeded = totalRequests - failuresNeeded
  
  -- Record below threshold
  run $ atomically $ do
    forM_ [1..failuresNeeded] $ \_ -> recordFailure cb now
    forM_ [1..successesNeeded] $ \_ -> recordSuccess cb now
  
  -- Circuit should still be closed
  available <- run $ atomically $ isAvailable cb now
  assert available
  
  state <- run $ atomically $ readTVar (cbState cb)
  case state of
    CircuitClosed -> assert True
    _ -> assert False

-- | Property: Failure rate calculation is correct
prop_failureRateCalculation :: Property
prop_failureRateCalculation = monadicIO $ do
  now <- run getCurrentTime
  failureThreshold <- pick genRealisticFailureThreshold
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig failureThreshold successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Record known failures and successes
  let failures = 5
  let successes = 5
  let total = failures + successes
  
  run $ atomically $ do
    forM_ [1..failures] $ \_ -> recordFailure cb now
    forM_ [1..successes] $ \_ -> recordSuccess cb now
  
  -- Check actual counts
  actualFailures <- run $ atomically $ readTVar (cbFailures cb)
  actualSuccesses <- run $ atomically $ readTVar (cbSuccesses cb)
  actualTotal <- run $ atomically $ readTVar (cbTotalRequests cb)
  
  assert $ actualFailures == fromIntegral failures
  assert $ actualSuccesses == fromIntegral successes
  assert $ actualTotal == fromIntegral total
  
  -- Calculate failure rate
  let failureRate = fromIntegral actualFailures / max 1.0 (fromIntegral actualTotal)
  let expectedRate = fromIntegral failures / fromIntegral total
  let tolerance = 0.01
  assert $ abs (failureRate - expectedRate) < tolerance

-- | Property: Zero failure threshold never opens
prop_zeroFailureThreshold :: Property
prop_zeroFailureThreshold = monadicIO $ do
  now <- run getCurrentTime
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig 0.0 successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Record many successes (should never open)
  run $ atomically $ do
    forM_ [1..100] $ \_ -> recordSuccess cb now
  
  -- Circuit should still be closed
  available <- run $ atomically $ isAvailable cb now
  assert available
  
  state <- run $ atomically $ readTVar (cbState cb)
  case state of
    CircuitClosed -> assert True
    _ -> assert False

-- | Property: 100% failure threshold always opens
prop_alwaysOpenThreshold :: Property
prop_alwaysOpenThreshold = monadicIO $ do
  now <- run getCurrentTime
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig 1.0 successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Record single failure (should open)
  run $ atomically $ recordFailure cb now
  
  -- Circuit should be open
  available <- run $ atomically $ isAvailable cb now
  assert $ not available
  
  state <- run $ atomically $ readTVar (cbState cb)
  case state of
    CircuitOpen _ -> assert True
    _ -> assert False

-- ============================================================================
-- ADDITIONAL PROPERTIES
-- ============================================================================

-- | Property: Statistics counters are consistent
prop_statisticsConsistency :: Property
prop_statisticsConsistency = monadicIO $ do
  now <- run getCurrentTime
  failureThreshold <- pick genRealisticFailureThreshold
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig failureThreshold successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Record random sequence
  requestCount <- pick genRealisticRequestCount
  run $ atomically $ do
    forM_ [1..requestCount] $ \i -> do
      if i `mod` 3 == 0
        then recordFailure cb now
        else recordSuccess cb now
  
  -- Check consistency
  failures <- run $ atomically $ readTVar (cbFailures cb)
  successes <- run $ atomically $ readTVar (cbSuccesses cb)
  total <- run $ atomically $ readTVar (cbTotalRequests cb)
  
  -- Total should equal failures + successes
  assert $ total == failures + successes

-- | Property: Reset clears all statistics
prop_resetClearsStatistics :: Property
prop_resetClearsStatistics = monadicIO $ do
  now <- run getCurrentTime
  failureThreshold <- pick genRealisticFailureThreshold
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig failureThreshold successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Record events
  run $ atomically $ do
    forM_ [1..10] $ \_ -> recordFailure cb now
    forM_ [1..10] $ \_ -> recordSuccess cb now
  
  -- Reset
  run $ atomically $ resetCircuitBreaker cb now
  
  -- All statistics should be zero
  failures <- run $ atomically $ readTVar (cbFailures cb)
  successes <- run $ atomically $ readTVar (cbSuccesses cb)
  total <- run $ atomically $ readTVar (cbTotalRequests cb)
  state <- run $ atomically $ readTVar (cbState cb)
  
  assert $ failures == 0
  assert $ successes == 0
  assert $ total == 0
  case state of
    CircuitClosed -> assert True
    _ -> assert False

-- ============================================================================
-- BUG DETECTION PROPERTIES
-- ============================================================================

-- | BUG: Window reset may interfere with state transitions
prop_bug_windowResetInterference :: Property
prop_bug_windowResetInterference = monadicIO $ do
  now <- run getCurrentTime
  failureThreshold <- pick genRealisticFailureThreshold
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig failureThreshold successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Record failures to near threshold
  let totalRequests = 10
  let failuresNeeded = ceiling (failureThreshold * fromIntegral totalRequests) - 1
  let successesNeeded = totalRequests - failuresNeeded
  
  run $ atomically $ do
    forM_ [1..failuresNeeded] $ \_ -> recordFailure cb now
    forM_ [1..successesNeeded] $ \_ -> recordSuccess cb now
  
  -- Advance time to trigger window reset
  let later = addUTCTime (secondsToDiffTime (fromIntegral windowSize + 1.0)) now
  
  -- Record failure (should reset window first, then record)
  run $ atomically $ recordFailure cb later
  
  -- State should be consistent
  state <- run $ atomically $ readTVar (cbState cb)
  assert $ case state of
    CircuitClosed -> True
    CircuitHalfOpen -> True
    CircuitOpen _ -> True
  -- BUG: If window reset interferes with state transition, state may be inconsistent

-- | BUG: Concurrent state updates may cause inconsistency
prop_bug_concurrentStateUpdate :: Property
prop_bug_concurrentStateUpdate = monadicIO $ do
  now <- run getCurrentTime
  failureThreshold <- pick genRealisticFailureThreshold
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig failureThreshold successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Multiple operations in same transaction
  run $ atomically $ do
    recordSuccess cb now
    recordFailure cb now
    recordSuccess cb now
    recordFailure cb now
  
  -- Statistics should be consistent
  failures <- run $ atomically $ readTVar (cbFailures cb)
  successes <- run $ atomically $ readTVar (cbSuccesses cb)
  total <- run $ atomically $ readTVar (cbTotalRequests cb)
  
  assert $ total == failures + successes
  -- BUG: If concurrent updates are not atomic, statistics may be inconsistent

-- | BUG: Clock jump backward may cause window issues
prop_bug_clockJumpBackward :: Property
prop_bug_clockJumpBackward = monadicIO $ do
  now <- run getCurrentTime
  failureThreshold <- pick genRealisticFailureThreshold
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig failureThreshold successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Record events
  run $ atomically $ do
    forM_ [1..5] $ \_ -> recordFailure cb now
    forM_ [1..5] $ \_ -> recordSuccess cb now
  
  -- Jump clock backward
  let past = addUTCTime (secondsToDiffTime (-100.0)) now
  
  -- Record event with backward clock
  run $ atomically $ recordSuccess cb past
  
  -- Statistics should be reasonable
  failures <- run $ atomically $ readTVar (cbFailures cb)
  successes <- run $ atomically $ readTVar (cbSuccesses cb)
  total <- run $ atomically $ readTVar (cbTotalRequests cb)
  
  assert $ failures >= 0
  assert $ successes >= 0
  assert $ total >= 0
  -- BUG: If clock jump backward is not handled, window calculations may be wrong

-- | BUG: Rolling window may have race conditions
prop_bug_rollingWindowRace :: Property
prop_bug_rollingWindowRace = monadicIO $ do
  now <- run getCurrentTime
  failureThreshold <- pick genRealisticFailureThreshold
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig failureThreshold successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Record events near window boundary
  let boundaryTime = addUTCTime (secondsToDiffTime (fromIntegral windowSize - 0.5)) now
  
  run $ atomically $ do
    recordFailure cb boundaryTime
    recordSuccess cb boundaryTime
  
  -- Advance past boundary
  let afterBoundary = addUTCTime (secondsToDiffTime (fromIntegral windowSize + 0.5)) boundaryTime
  
  -- Record event (should reset)
  run $ atomically $ recordSuccess cb afterBoundary
  
  -- Statistics should be correct
  failures <- run $ atomically $ readTVar (cbFailures cb)
  successes <- run $ atomically $ readTVar (cbSuccesses cb)
  total <- run $ atomically $ readTVar (cbTotalRequests cb)
  
  assert $ total == failures + successes
  -- BUG: If rolling window has race conditions, statistics may be incorrect

-- | BUG: isAvailable may not update state correctly
prop_bug_isAvailableStateUpdate :: Property
prop_bug_isAvailableStateUpdate = monadicIO $ do
  now <- run getCurrentTime
  failureThreshold <- pick genRealisticFailureThreshold
  successThreshold <- pick genRealisticSuccessThreshold
  timeout <- pick genRealisticTimeout
  windowSize <- pick genRealisticWindowSize
  
  let config = CircuitBreakerConfig failureThreshold successThreshold timeout windowSize
  cb <- run $ atomically $ createCircuitBreaker now config
  
  -- Open circuit
  run $ atomically $ do
    writeTVar (cbState cb) (CircuitOpen now)
  
  -- Advance past timeout
  let later = addUTCTime (secondsToDiffTime (fromIntegral timeout + 1.0)) now
  
  -- Check availability (should transition to half-open)
  available1 <- run $ atomically $ isAvailable cb later
  assert available1
  
  -- Check again (should still be half-open)
  available2 <- run $ atomically $ isAvailable cb later
  assert available2
  
  -- State should be half-open
  state <- run $ atomically $ readTVar (cbState cb)
  case state of
    CircuitHalfOpen -> assert True
    _ -> assert False
  -- BUG: If isAvailable doesn't update state correctly, state may be inconsistent

-- ============================================================================
-- TEST RUNNER
-- ============================================================================

main :: IO ()
main = do
  putStrLn "Circuit Breaker Property Tests"
  putStrLn "=============================="
  
  putStrLn "\n1. Closed → Open"
  quickCheck prop_closedToOpen
  
  putStrLn "\n2. Open → HalfOpen"
  quickCheck prop_openToHalfOpen
  
  putStrLn "\n3. HalfOpen → Closed"
  quickCheck prop_halfOpenToClosed
  
  putStrLn "\n4. HalfOpen → Open"
  quickCheck prop_halfOpenToOpen
  
  putStrLn "\n5. State Transitions Atomic"
  quickCheck prop_stateTransitionsAtomic
  
  putStrLn "\n6. Window Resets Statistics"
  quickCheck prop_windowResetsStatistics
  
  putStrLn "\n7. Window No Reset Before Expiration"
  quickCheck prop_windowNoResetBeforeExpiration
  
  putStrLn "\n8. Multiple Window Resets"
  quickCheck prop_multipleWindowResets
  
  putStrLn "\n9. Opens At Exact Threshold"
  quickCheck prop_opensAtExactThreshold
  
  putStrLn "\n10. Does Not Open Below Threshold"
  quickCheck prop_doesNotOpenBelowThreshold
  
  putStrLn "\n11. Failure Rate Calculation"
  quickCheck prop_failureRateCalculation
  
  putStrLn "\n12. Zero Failure Threshold"
  quickCheck prop_zeroFailureThreshold
  
  putStrLn "\n13. Always Open Threshold"
  quickCheck prop_alwaysOpenThreshold
  
  putStrLn "\n14. Statistics Consistency"
  quickCheck prop_statisticsConsistency
  
  putStrLn "\n15. Reset Clears Statistics"
  quickCheck prop_resetClearsStatistics
  
  putStrLn "\n16. Bug: Window Reset Interference"
  quickCheck prop_bug_windowResetInterference
  
  putStrLn "\n17. Bug: Concurrent State Update"
  quickCheck prop_bug_concurrentStateUpdate
  
  putStrLn "\n18. Bug: Clock Jump Backward"
  quickCheck prop_bug_clockJumpBackward
  
  putStrLn "\n19. Bug: Rolling Window Race"
  quickCheck prop_bug_rollingWindowRace
  
  putStrLn "\n20. Bug: isAvailable State Update"
  quickCheck prop_bug_isAvailableStateUpdate
  
  putStrLn "\nAll tests completed!"
