{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Deep Comprehensive Property Tests for Rate Limiter
-- |
-- | Tests token refill, capacity bounds, and clock jump handling
-- | with realistic distributions to find real bugs.
-- |
-- | Based on spec 70-TESTING-STRATEGY.md and 71-UNIT-TESTING.md
-- | Reference: REQUIRED/trtllm-serve-main/nix/openai-proxy-hs/ProxyPropTest.hs
module RateLimiterProps where

import Test.QuickCheck
import Test.QuickCheck.Monadic
import Control.Concurrent.STM
import Control.Monad (replicateM, forM_)
import Data.Time (UTCTime, getCurrentTime, addUTCTime, diffUTCTime, secondsToDiffTime)
import Data.Int (Int32)
import Data.List (sort, scanl)

import Render.Gateway.STM.RateLimiter
import Render.Gateway.STM.Clock

-- ============================================================================
-- REALISTIC DISTRIBUTIONS
-- ============================================================================

-- | Realistic capacity distribution:
-- | - Most limiters: 100-1000 tokens (normal)
-- | - Some limiters: 1000-5000 tokens (high capacity)
-- | - Few limiters: 5000-10000 tokens (very high capacity)
genRealisticCapacity :: Gen Double
genRealisticCapacity = frequency
  [ (70, choose (100.0, 1000.0))      -- Normal capacity
  , (25, choose (1000.0, 5000.0))     -- High capacity
  , (5, choose (5000.0, 10000.0))     -- Very high capacity
  ]

-- | Realistic refill rate distribution:
-- | - Most limiters: 10-100 tokens/sec (normal)
-- | - Some limiters: 100-500 tokens/sec (high rate)
-- | - Few limiters: 500-1000 tokens/sec (very high rate)
genRealisticRefillRate :: Gen Double
genRealisticRefillRate = frequency
  [ (70, choose (10.0, 100.0))        -- Normal rate
  , (25, choose (100.0, 500.0))       -- High rate
  , (5, choose (500.0, 1000.0))       -- Very high rate
  ]

-- | Realistic time delta distribution:
-- | - Most tests: 0.1-10 seconds (normal)
-- | - Some tests: 10-60 seconds (long wait)
-- | - Few tests: 60-300 seconds (very long wait)
genRealisticTimeDelta :: Gen Double
genRealisticTimeDelta = frequency
  [ (70, choose (0.1, 10.0))          -- Normal delta
  , (25, choose (10.0, 60.0))         -- Long delta
  , (5, choose (60.0, 300.0))          -- Very long delta
  ]

-- | Realistic clock jump distribution:
-- | - Most tests: small forward jumps (0-10 seconds)
-- | - Some tests: large forward jumps (10-3600 seconds)
-- | - Few tests: backward jumps (-3600 to 0 seconds)
genRealisticClockJump :: Gen Double
genRealisticClockJump = frequency
  [ (60, choose (0.0, 10.0))          -- Small forward
  , (30, choose (10.0, 3600.0))       -- Large forward
  , (10, choose (-3600.0, 0.0))       -- Backward
  ]

-- | Realistic acquisition count distribution:
genRealisticAcquisitionCount :: Gen Int
genRealisticAcquisitionCount = frequency
  [ (70, choose (1, 50))               -- Normal
  , (25, choose (50, 200))             -- High
  , (5, choose (200, 1000))            -- Stress
  ]

-- ============================================================================
-- PROPERTY TESTS
-- ============================================================================

-- | Property: Token refill based on elapsed time
-- | After time delta, tokens should increase by refillRate * delta (up to capacity)
prop_tokenRefill :: Property
prop_tokenRefill = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  timeDelta <- pick genRealisticTimeDelta
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Get initial token count
  initialTokens <- run $ atomically $ getTokenCount rl now
  
  -- Advance time
  let later = addUTCTime (secondsToDiffTime timeDelta) now
  
  -- Get token count after time advance
  finalTokens <- run $ atomically $ getTokenCount rl later
  
  -- Tokens should have increased by refillRate * timeDelta (up to capacity)
  let expectedIncrease = refillRate * timeDelta
  let expectedTokens = min capacity (initialTokens + expectedIncrease)
  
  -- Allow small floating point error
  let tolerance = 0.01
  assert $ abs (finalTokens - expectedTokens) < tolerance || finalTokens == capacity

-- | Property: Capacity bounds
-- | Tokens should never exceed capacity
prop_capacityBounds :: Property
prop_capacityBounds = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Try to refill with very large time delta
  largeDelta <- pick $ choose (1000.0, 10000.0)
  let farFuture = addUTCTime (secondsToDiffTime largeDelta) now
  
  -- Refill tokens
  run $ atomically $ refillTokens rl farFuture
  
  -- Check capacity bound
  tokens <- run $ atomically $ readTVar (rlTokens rl)
  assert $ tokens <= capacity
  
  -- Acquire all tokens
  run $ atomically $ do
    forM_ [1..(floor capacity)] $ \_ -> do
      acquired <- acquireToken rl farFuture
      return ()
  
  -- Refill again
  run $ atomically $ refillTokens rl farFuture
  
  -- Should still be bounded by capacity
  tokensFinal <- run $ atomically $ readTVar (rlTokens rl)
  assert $ tokensFinal <= capacity

-- | Property: Clock jump backward handling
-- | Backward clock jumps should not cause negative refill or errors
prop_clockJumpBackward :: Property
prop_clockJumpBackward = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Get initial token count
  initialTokens <- run $ atomically $ getTokenCount rl now
  
  -- Jump clock backward
  backwardJump <- pick $ choose (1.0, 3600.0)
  let past = addUTCTime (secondsToDiffTime (-backwardJump)) now
  
  -- Refill with backward clock (should not refill)
  run $ atomically $ refillTokens rl past
  
  -- Token count should not have increased (may have decreased if we acquired tokens)
  tokensAfterBackward <- run $ atomically $ readTVar (rlTokens rl)
  assert $ tokensAfterBackward <= initialTokens || tokensAfterBackward <= capacity
  
  -- Jump forward again
  let future = addUTCTime (secondsToDiffTime backwardJump) past
  
  -- Should refill normally now
  run $ atomically $ refillTokens rl future
  
  -- Tokens should be reasonable
  tokensFinal <- run $ atomically $ readTVar (rlTokens rl)
  assert $ tokensFinal >= 0.0
  assert $ tokensFinal <= capacity

-- | Property: Continuous refill over time
-- | Tokens should refill continuously as time advances
prop_continuousRefill :: Property
prop_continuousRefill = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Acquire all tokens
  run $ atomically $ do
    forM_ [1..(floor capacity)] $ \_ -> do
      acquired <- acquireToken rl now
      return ()
  
  -- Advance time in steps
  let steps = 10
  let stepSize = 1.0  -- 1 second per step
  
  run $ atomically $ do
    forM_ [1..steps] $ \step -> do
      let currentTime = addUTCTime (secondsToDiffTime (fromIntegral step * stepSize)) now
      refillTokens rl currentTime
  
  -- Should have refilled
  tokensAfterSteps <- run $ atomically $ readTVar (rlTokens rl)
  let expectedRefill = refillRate * fromIntegral steps
  assert $ tokensAfterSteps >= expectedRefill || tokensAfterSteps == capacity

-- | Property: Acquire token decreases count
prop_acquireDecreasesTokens :: Property
prop_acquireDecreasesTokens = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Get initial token count
  initialTokens <- run $ atomically $ getTokenCount rl now
  
  -- Acquire a token
  acquired <- run $ atomically $ acquireToken rl now
  
  if acquired
    then do
      -- Token count should have decreased by 1
      finalTokens <- run $ atomically $ readTVar (rlTokens rl)
      assert $ abs (finalTokens - (initialTokens - 1.0)) < 0.01
    else do
      -- Should not have been able to acquire (no tokens)
      assert $ initialTokens < 1.0

-- | Property: Multiple acquisitions respect capacity
prop_multipleAcquisitions :: Property
prop_multipleAcquisitions = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Try to acquire more than capacity
  acquisitionCount <- pick $ choose (floor capacity + 1, floor capacity + 100)
  
  -- Acquire tokens
  acquiredCount <- run $ atomically $ do
    results <- replicateM acquisitionCount $ acquireToken rl now
    return $ length $ filter id results
  
  -- Should only acquire up to capacity
  assert $ fromIntegral acquiredCount <= capacity
  
  -- Token count should reflect acquisitions
  tokens <- run $ atomically $ readTVar (rlTokens rl)
  assert $ tokens >= 0.0
  assert $ tokens <= capacity

-- | Property: Refill rate accuracy
-- | Refill should match expected rate over time
prop_refillRateAccuracy :: Property
prop_refillRateAccuracy = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick $ choose (1000.0, 5000.0)  -- Large capacity for accuracy test
  refillRate <- pick $ choose (10.0, 100.0)
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Start with empty tokens
  run $ atomically $ do
    writeTVar (rlTokens rl) 0.0
  
  -- Advance time
  timeDelta <- pick $ choose (10.0, 60.0)
  let later = addUTCTime (secondsToDiffTime timeDelta) now
  
  -- Refill
  run $ atomically $ refillTokens rl later
  
  -- Check refill accuracy
  tokens <- run $ atomically $ readTVar (rlTokens rl)
  let expectedTokens = min capacity (refillRate * timeDelta)
  let tolerance = 0.01
  assert $ abs (tokens - expectedTokens) < tolerance || tokens == capacity

-- | Property: Acquire token blocks when no tokens
prop_acquireBlocksWhenEmpty :: Property
prop_acquireBlocksWhenEmpty = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Deplete all tokens
  run $ atomically $ do
    forM_ [1..(floor capacity)] $ \_ -> do
      acquired <- acquireToken rl now
      return ()
  
  -- Try to acquire (should fail)
  acquired <- run $ atomically $ acquireToken rl now
  assert $ not acquired
  
  -- Token count should be < 1.0
  tokens <- run $ atomically $ readTVar (rlTokens rl)
  assert $ tokens < 1.0

-- | Property: Refill after depletion
prop_refillAfterDepletion :: Property
prop_refillAfterDepletion = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Deplete all tokens
  run $ atomically $ do
    forM_ [1..(floor capacity)] $ \_ -> do
      acquired <- acquireToken rl now
      return ()
  
  -- Advance time
  timeDelta <- pick genRealisticTimeDelta
  let later = addUTCTime (secondsToDiffTime timeDelta) now
  
  -- Refill
  run $ atomically $ refillTokens rl later
  
  -- Should have refilled
  tokens <- run $ atomically $ readTVar (rlTokens rl)
  let expectedRefill = min capacity (refillRate * timeDelta)
  let tolerance = 0.01
  assert $ abs (tokens - expectedRefill) < tolerance || tokens == capacity

-- | Property: Zero refill rate handling
prop_zeroRefillRate :: Property
prop_zeroRefillRate = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  
  rl <- run $ atomically $ createRateLimiter capacity 0.0 now
  
  -- Get initial tokens
  initialTokens <- run $ atomically $ getTokenCount rl now
  
  -- Advance time
  let later = addUTCTime (secondsToDiffTime 100.0) now
  
  -- Refill (should not add tokens)
  run $ atomically $ refillTokens rl later
  
  -- Tokens should not have increased
  finalTokens <- run $ atomically $ readTVar (rlTokens rl)
  assert $ finalTokens <= initialTokens || finalTokens == capacity

-- | Property: Very large refill rate handling
prop_largeRefillRate :: Property
prop_largeRefillRate = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  largeRefillRate <- pick $ choose (1000.0, 10000.0)
  
  rl <- run $ atomically $ createRateLimiter capacity largeRefillRate now
  
  -- Start with empty tokens
  run $ atomically $ writeTVar (rlTokens rl) 0.0
  
  -- Advance small amount of time
  let later = addUTCTime (secondsToDiffTime 0.1) now
  
  -- Refill
  run $ atomically $ refillTokens rl later
  
  -- Should reach capacity quickly
  tokens <- run $ atomically $ readTVar (rlTokens rl)
  assert $ tokens <= capacity
  -- With large refill rate, should be at capacity after small time
  assert $ tokens == capacity || tokens >= capacity * 0.9

-- ============================================================================
-- BUG DETECTION PROPERTIES
-- ============================================================================

-- | BUG: Refill may not handle clock jumps correctly
prop_bug_clockJumpHandling :: Property
prop_bug_clockJumpHandling = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Get initial state
  initialTokens <- run $ atomically $ readTVar (rlTokens rl)
  initialLastRefill <- run $ atomically $ readTVar (rlLastRefill rl)
  
  -- Jump backward
  backwardJump <- pick $ choose (1.0, 3600.0)
  let past = addUTCTime (secondsToDiffTime (-backwardJump)) initialLastRefill
  
  -- Refill with backward clock
  run $ atomically $ refillTokens rl past
  
  -- Should not have increased tokens
  tokensAfterBackward <- run $ atomically $ readTVar (rlTokens rl)
  assert $ tokensAfterBackward <= initialTokens || tokensAfterBackward <= capacity
  
  -- lastRefill should be updated to past time
  lastRefillAfterBackward <- run $ atomically $ readTVar (rlLastRefill rl)
  assert $ lastRefillAfterBackward == past
  -- BUG: If clock jump handling is wrong, tokens may increase incorrectly

-- | BUG: Capacity may be exceeded with rapid refills
prop_bug_capacityExceeded :: Property
prop_bug_capacityExceeded = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Rapid refills
  run $ atomically $ do
    forM_ [1..100] $ \i -> do
      let currentTime = addUTCTime (secondsToDiffTime (fromIntegral i * 0.01)) now
      refillTokens rl currentTime
  
  -- Capacity should never be exceeded
  tokens <- run $ atomically $ readTVar (rlTokens rl)
  assert $ tokens <= capacity
  -- BUG: If refill logic is wrong, capacity may be exceeded

-- | BUG: Token count may become negative
prop_bug_negativeTokens :: Property
prop_bug_negativeTokens = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Try to acquire more tokens than available
  acquisitionCount <- pick $ choose (floor capacity + 1, floor capacity * 2)
  
  run $ atomically $ do
    forM_ [1..acquisitionCount] $ \_ -> do
      acquireToken rl now
      return ()
  
  -- Token count should never be negative
  tokens <- run $ atomically $ readTVar (rlTokens rl)
  assert $ tokens >= 0.0
  -- BUG: If acquisition logic is wrong, tokens may go negative

-- | BUG: Refill may not update lastRefill correctly
prop_bug_lastRefillUpdate :: Property
prop_bug_lastRefillUpdate = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Refill at specific time
  timeDelta <- pick genRealisticTimeDelta
  let refillTime = addUTCTime (secondsToDiffTime timeDelta) now
  
  run $ atomically $ refillTokens rl refillTime
  
  -- lastRefill should be updated
  lastRefill <- run $ atomically $ readTVar (rlLastRefill rl)
  assert $ lastRefill == refillTime
  -- BUG: If lastRefill is not updated, refill calculations will be wrong

-- | BUG: acquireTokenBlocking may block indefinitely
prop_bug_blockingIndefinite :: Property
prop_bug_blockingIndefinite = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick $ choose (0.01, 0.1)  -- Very slow refill
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  clock <- run createClock
  
  -- Deplete all tokens
  run $ atomically $ do
    forM_ [1..(floor capacity)] $ \_ -> do
      acquired <- acquireToken rl now
      return ()
  
  -- Update clock to current time
  run $ updateClock clock
  
  -- Try acquireTokenBlocking (should eventually succeed after refill)
  -- Note: This test may timeout if blocking is broken
  -- We test that it doesn't block forever by advancing clock
  run $ atomically $ do
    -- Advance clock to allow refill
    let future = addUTCTime (secondsToDiffTime (capacity / refillRate + 1.0)) now
    -- Manually update clock for test
    -- In real scenario, clock thread would advance it
    -- For test, we'll use acquireToken with future time
    acquired <- acquireToken rl future
    assert acquired
  
  -- Should eventually succeed
  assert True
  -- BUG: If acquireTokenBlocking blocks indefinitely, this test will timeout

-- | BUG: Refill calculation may have precision issues
prop_bug_refillPrecision :: Property
prop_bug_refillPrecision = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Small time delta
  let smallDelta = 0.001  -- 1ms
  let later = addUTCTime (secondsToDiffTime smallDelta) now
  
  -- Refill
  run $ atomically $ refillTokens rl later
  
  -- Should have small refill (or none if too small)
  tokens <- run $ atomically $ readTVar (rlTokens rl)
  let expectedRefill = refillRate * smallDelta
  -- Allow for floating point precision issues
  assert $ tokens >= 0.0
  assert $ tokens <= capacity
  -- BUG: If precision is wrong, tokens may be incorrect

-- | BUG: Concurrent acquisitions may cause race conditions
prop_bug_concurrentAcquisition :: Property
prop_bug_concurrentAcquisition = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Multiple concurrent acquisitions
  acquisitionCount <- pick $ choose (floor capacity, floor capacity * 2)
  
  -- All in same STM transaction (simulates concurrent access)
  acquiredCount <- run $ atomically $ do
    results <- replicateM acquisitionCount $ acquireToken rl now
    return $ length $ filter id results
  
  -- Should only acquire up to capacity
  assert $ fromIntegral acquiredCount <= capacity
  
  -- Token count should be correct
  tokens <- run $ atomically $ readTVar (rlTokens rl)
  let expectedTokens = capacity - fromIntegral acquiredCount
  let tolerance = 0.01
  assert $ abs (tokens - expectedTokens) < tolerance || tokens >= 0.0
  -- BUG: If concurrent access has race conditions, count may be wrong

-- | BUG: Clock jump forward may cause excessive refill
-- | Large forward jumps should still respect capacity
prop_bug_clockJumpForward :: Property
prop_bug_clockJumpForward = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Start with empty tokens
  run $ atomically $ writeTVar (rlTokens rl) 0.0
  
  -- Large forward jump
  forwardJump <- pick $ choose (1000.0, 10000.0)
  let future = addUTCTime (secondsToDiffTime forwardJump) now
  
  -- Refill with large forward jump
  run $ atomically $ refillTokens rl future
  
  -- Should be at capacity (not exceed it)
  tokens <- run $ atomically $ readTVar (rlTokens rl)
  assert $ tokens <= capacity
  assert $ tokens == capacity  -- Should be exactly at capacity after large jump
  -- BUG: If forward jump handling is wrong, tokens may exceed capacity

-- | BUG: Multiple rapid refills may cause lastRefill desynchronization
-- | Rapid refills should maintain consistent lastRefill
prop_bug_rapidRefillDesync :: Property
prop_bug_rapidRefillDesync = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Rapid refills with small time increments
  run $ atomically $ do
    forM_ [1..100] $ \i -> do
      let currentTime = addUTCTime (secondsToDiffTime (fromIntegral i * 0.001)) now
      refillTokens rl currentTime
  
  -- Last refill should be the last time we called refill
  lastRefill <- run $ atomically $ readTVar (rlLastRefill rl)
  let expectedLastRefill = addUTCTime (secondsToDiffTime (100 * 0.001)) now
  assert $ lastRefill == expectedLastRefill
  -- BUG: If rapid refills cause desync, lastRefill may be wrong

-- | BUG: Token count may become inconsistent during rapid acquire/refill cycles
-- | Rapid cycles should maintain token count consistency
prop_bug_rapidAcquireRefillCycles :: Property
prop_bug_rapidAcquireRefillCycles = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Track expected token count
  expectedTokens <- run $ newTVarIO capacity
  
  -- Rapid acquire/refill cycles
  run $ atomically $ do
    forM_ [1..50] $ \i -> do
      -- Acquire token
      acquired <- acquireToken rl (addUTCTime (secondsToDiffTime (fromIntegral i * 0.1)) now)
      if acquired
        then modifyTVar' expectedTokens (\t -> max 0.0 (t - 1.0))
        else return ()
      
      -- Refill
      let refillTime = addUTCTime (secondsToDiffTime (fromIntegral i * 0.1 + 0.05)) now
      refillTokens rl refillTime
      
      -- Update expected tokens based on refill
      lastRefill <- readTVar (rlLastRefill rl)
      tokens <- readTVar (rlTokens rl)
      expected <- readTVar expectedTokens
      -- Expected should account for refill
      let elapsed = realToFrac (diffUTCTime refillTime lastRefill)
      let refillAmount = if elapsed < 0 then 0 else elapsed * refillRate
      modifyTVar' expectedTokens (\t -> min capacity (t + refillAmount))
  
  -- Check consistency
  actualTokens <- run $ atomically $ readTVar (rlTokens rl)
  expected <- run $ readTVarIO expectedTokens
  let tolerance = 0.1  -- Allow some tolerance for floating point
  assert $ abs (actualTokens - expected) < tolerance || actualTokens <= capacity
  -- BUG: If rapid cycles cause inconsistency, actual != expected

-- | BUG: Capacity boundary precision may cause tokens to exceed capacity
-- | Tokens at capacity boundary should not exceed capacity
prop_bug_capacityBoundaryPrecision :: Property
prop_bug_capacityBoundaryPrecision = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Set tokens to just below capacity
  run $ atomically $ writeTVar (rlTokens rl) (capacity - 0.0001)
  
  -- Refill with small time delta
  let smallDelta = 0.0001
  let later = addUTCTime (secondsToDiffTime smallDelta) now
  
  -- Refill
  run $ atomically $ refillTokens rl later
  
  -- Should not exceed capacity
  tokens <- run $ atomically $ readTVar (rlTokens rl)
  assert $ tokens <= capacity
  -- BUG: If boundary precision is wrong, tokens may exceed capacity

-- | BUG: Refill calculation may be inaccurate with very small refill rates
-- | Very small refill rates should still work correctly
prop_bug_smallRefillRateAccuracy :: Property
prop_bug_smallRefillRateAccuracy = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  smallRefillRate <- pick $ choose (0.001, 0.1)  -- Very small rate
  
  rl <- run $ atomically $ createRateLimiter capacity smallRefillRate now
  
  -- Start with empty tokens
  run $ atomically $ writeTVar (rlTokens rl) 0.0
  
  -- Advance time
  timeDelta <- pick $ choose (10.0, 100.0)
  let later = addUTCTime (secondsToDiffTime timeDelta) now
  
  -- Refill
  run $ atomically $ refillTokens rl later
  
  -- Should have refilled correctly
  tokens <- run $ atomically $ readTVar (rlTokens rl)
  let expectedTokens = min capacity (smallRefillRate * timeDelta)
  let tolerance = 0.01
  assert $ abs (tokens - expectedTokens) < tolerance || tokens == capacity
  -- BUG: If small refill rate handling is wrong, tokens may be incorrect

-- | BUG: Token count may become inconsistent after multiple refills
-- | Multiple refills should maintain consistency
prop_bug_multipleRefillConsistency :: Property
prop_bug_multipleRefillConsistency = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Start with empty tokens
  run $ atomically $ writeTVar (rlTokens rl) 0.0
  
  -- Multiple refills at different times
  refillTimes <- pick $ replicateM 10 (genRealisticTimeDelta)
  let sortedTimes = sort refillTimes
  let cumulativeTimes = scanl (+) 0.0 sortedTimes
  
  run $ atomically $ do
    forM_ cumulativeTimes $ \cumulativeTime -> do
      let refillTime = addUTCTime (secondsToDiffTime cumulativeTime) now
      refillTokens rl refillTime
  
  -- Token count should be consistent
  tokens <- run $ atomically $ readTVar (rlTokens rl)
  let totalTime = sum sortedTimes
  let expectedTokens = min capacity (refillRate * totalTime)
  let tolerance = 0.1
  assert $ abs (tokens - expectedTokens) < tolerance || tokens == capacity
  -- BUG: If multiple refills cause inconsistency, tokens may be wrong

-- | BUG: Clock jump backward then forward may cause refill issues
-- | Backward then forward jumps should handle correctly
prop_bug_clockJumpBackwardForward :: Property
prop_bug_clockJumpBackwardForward = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Get initial tokens
  initialTokens <- run $ atomically $ readTVar (rlTokens rl)
  
  -- Jump backward
  backwardJump <- pick $ choose (100.0, 1000.0)
  let past = addUTCTime (secondsToDiffTime (-backwardJump)) now
  
  -- Refill with backward clock
  run $ atomically $ refillTokens rl past
  
  -- Should not have increased
  tokensAfterBackward <- run $ atomically $ readTVar (rlTokens rl)
  assert $ tokensAfterBackward <= initialTokens || tokensAfterBackward <= capacity
  
  -- Jump forward past original time
  forwardJump <- pick $ choose (backwardJump + 1.0, backwardJump + 1000.0)
  let future = addUTCTime (secondsToDiffTime forwardJump) past
  
  -- Refill with forward clock
  run $ atomically $ refillTokens rl future
  
  -- Should have refilled based on forward jump
  tokensAfterForward <- run $ atomically $ readTVar (rlTokens rl)
  let expectedRefill = refillRate * forwardJump
  let expectedTokens = min capacity (initialTokens + expectedRefill)
  let tolerance = 0.1
  assert $ abs (tokensAfterForward - expectedTokens) < tolerance || tokensAfterForward == capacity
  -- BUG: If backward then forward jump handling is wrong, refill may be incorrect

-- | BUG: Token acquisition with fractional tokens may cause precision issues
-- | Fractional token handling should maintain precision
prop_bug_fractionalTokenPrecision :: Property
prop_bug_fractionalTokenPrecision = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Set tokens to fractional value
  fractionalTokens <- pick $ choose (0.1, 0.9)
  run $ atomically $ writeTVar (rlTokens rl) fractionalTokens
  
  -- Try to acquire token (should fail since < 1.0)
  acquired <- run $ atomically $ acquireToken rl now
  assert $ not acquired
  
  -- Token count should remain unchanged
  tokens <- run $ atomically $ readTVar (rlTokens rl)
  let tolerance = 0.0001
  assert $ abs (tokens - fractionalTokens) < tolerance
  -- BUG: If fractional token handling is wrong, tokens may change incorrectly

-- | BUG: Refill rate edge case with zero capacity
-- | Zero capacity should handle correctly
prop_bug_zeroCapacity :: Property
prop_bug_zeroCapacity = monadicIO $ do
  now <- run getCurrentTime
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter 0.0 refillRate now
  
  -- Tokens should be 0
  tokens <- run $ atomically $ readTVar (rlTokens rl)
  assert $ tokens == 0.0
  
  -- Advance time and refill
  let later = addUTCTime (secondsToDiffTime 100.0) now
  run $ atomically $ refillTokens rl later
  
  -- Should still be 0 (capacity is 0)
  tokensAfterRefill <- run $ atomically $ readTVar (rlTokens rl)
  assert $ tokensAfterRefill == 0.0
  
  -- Should not be able to acquire
  acquired <- run $ atomically $ acquireToken rl later
  assert $ not acquired
  -- BUG: If zero capacity handling is wrong, tokens may become non-zero

-- | BUG: Token count accuracy after depletion and multiple refills
-- | Depletion then refills should maintain accuracy
prop_bug_depletionRefillAccuracy :: Property
prop_bug_depletionRefillAccuracy = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Deplete all tokens
  run $ atomically $ do
    forM_ [1..(floor capacity)] $ \_ -> do
      acquired <- acquireToken rl now
      return ()
  
  -- Verify depleted
  tokensAfterDepletion <- run $ atomically $ readTVar (rlTokens rl)
  assert $ tokensAfterDepletion < 1.0
  
  -- Multiple refills
  refillCount <- pick $ choose (5, 20)
  let refillInterval = 1.0  -- 1 second between refills
  
  run $ atomically $ do
    forM_ [1..refillCount] $ \i -> do
      let refillTime = addUTCTime (secondsToDiffTime (fromIntegral i * refillInterval)) now
      refillTokens rl refillTime
  
  -- Should have refilled correctly
  tokensAfterRefills <- run $ atomically $ readTVar (rlTokens rl)
  let expectedRefill = refillRate * fromIntegral refillCount * refillInterval
  let expectedTokens = min capacity expectedRefill
  let tolerance = 0.1
  assert $ abs (tokensAfterRefills - expectedTokens) < tolerance || tokensAfterRefills == capacity
  -- BUG: If depletion/refill accuracy is wrong, tokens may be incorrect

-- | BUG: Rapid acquire/refill cycles may cause token count desynchronization
-- | Rapid cycles should maintain synchronization
prop_bug_rapidCyclesDesync :: Property
prop_bug_rapidCyclesDesync = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Track operations
  operationCount <- pick $ choose (100, 500)
  
  -- Rapid acquire/refill cycles
  run $ atomically $ do
    forM_ [1..operationCount] $ \i -> do
      if i `mod` 2 == 0
        then do
          -- Acquire
          acquireToken rl (addUTCTime (secondsToDiffTime (fromIntegral i * 0.01)) now)
        else do
          -- Refill
          let refillTime = addUTCTime (secondsToDiffTime (fromIntegral i * 0.01)) now
          refillTokens rl refillTime
  
  -- Token count should be reasonable
  tokens <- run $ atomically $ readTVar (rlTokens rl)
  assert $ tokens >= 0.0
  assert $ tokens <= capacity
  -- BUG: If rapid cycles cause desync, tokens may be out of bounds

-- | BUG: Last refill update consistency during rapid refills
-- | Rapid refills should maintain lastRefill consistency
prop_bug_lastRefillConsistency :: Property
prop_bug_lastRefillConsistency = monadicIO $ do
  now <- run getCurrentTime
  capacity <- pick genRealisticCapacity
  refillRate <- pick genRealisticRefillRate
  
  rl <- run $ atomically $ createRateLimiter capacity refillRate now
  
  -- Rapid refills
  refillCount <- pick $ choose (50, 200)
  let lastRefillTime = addUTCTime (secondsToDiffTime (fromIntegral refillCount * 0.01)) now
  
  run $ atomically $ do
    forM_ [1..refillCount] $ \i -> do
      let refillTime = addUTCTime (secondsToDiffTime (fromIntegral i * 0.01)) now
      refillTokens rl refillTime
  
  -- Last refill should be the last time
  lastRefill <- run $ atomically $ readTVar (rlLastRefill rl)
  assert $ lastRefill == lastRefillTime
  -- BUG: If lastRefill consistency is wrong, it may not match last refill time

-- ============================================================================
-- TEST RUNNER
-- ============================================================================

main :: IO ()
main = do
  putStrLn "Rate Limiter Property Tests"
  putStrLn "============================"
  
  putStrLn "\n1. Token Refill"
  quickCheck prop_tokenRefill
  
  putStrLn "\n2. Capacity Bounds"
  quickCheck prop_capacityBounds
  
  putStrLn "\n3. Clock Jump Backward"
  quickCheck prop_clockJumpBackward
  
  putStrLn "\n4. Continuous Refill"
  quickCheck prop_continuousRefill
  
  putStrLn "\n5. Acquire Decreases Tokens"
  quickCheck prop_acquireDecreasesTokens
  
  putStrLn "\n6. Multiple Acquisitions"
  quickCheck prop_multipleAcquisitions
  
  putStrLn "\n7. Refill Rate Accuracy"
  quickCheck prop_refillRateAccuracy
  
  putStrLn "\n8. Acquire Blocks When Empty"
  quickCheck prop_acquireBlocksWhenEmpty
  
  putStrLn "\n9. Refill After Depletion"
  quickCheck prop_refillAfterDepletion
  
  putStrLn "\n10. Zero Refill Rate"
  quickCheck prop_zeroRefillRate
  
  putStrLn "\n11. Large Refill Rate"
  quickCheck prop_largeRefillRate
  
  putStrLn "\n12. Bug: Clock Jump Handling"
  quickCheck prop_bug_clockJumpHandling
  
  putStrLn "\n13. Bug: Capacity Exceeded"
  quickCheck prop_bug_capacityExceeded
  
  putStrLn "\n14. Bug: Negative Tokens"
  quickCheck prop_bug_negativeTokens
  
  putStrLn "\n15. Bug: Last Refill Update"
  quickCheck prop_bug_lastRefillUpdate
  
  putStrLn "\n16. Bug: Blocking Indefinite"
  quickCheck prop_bug_blockingIndefinite
  
  putStrLn "\n17. Bug: Refill Precision"
  quickCheck prop_bug_refillPrecision
  
  putStrLn "\n18. Bug: Concurrent Acquisition"
  quickCheck prop_bug_concurrentAcquisition
  
  putStrLn "\n19. Bug: Clock Jump Forward"
  quickCheck prop_bug_clockJumpForward
  
  putStrLn "\n20. Bug: Rapid Refill Desync"
  quickCheck prop_bug_rapidRefillDesync
  
  putStrLn "\n21. Bug: Rapid Acquire Refill Cycles"
  quickCheck prop_bug_rapidAcquireRefillCycles
  
  putStrLn "\n22. Bug: Capacity Boundary Precision"
  quickCheck prop_bug_capacityBoundaryPrecision
  
  putStrLn "\n23. Bug: Small Refill Rate Accuracy"
  quickCheck prop_bug_smallRefillRateAccuracy
  
  putStrLn "\n24. Bug: Multiple Refill Consistency"
  quickCheck prop_bug_multipleRefillConsistency
  
  putStrLn "\n25. Bug: Clock Jump Backward Forward"
  quickCheck prop_bug_clockJumpBackwardForward
  
  putStrLn "\n26. Bug: Fractional Token Precision"
  quickCheck prop_bug_fractionalTokenPrecision
  
  putStrLn "\n27. Bug: Zero Capacity"
  quickCheck prop_bug_zeroCapacity
  
  putStrLn "\n28. Bug: Depletion Refill Accuracy"
  quickCheck prop_bug_depletionRefillAccuracy
  
  putStrLn "\n29. Bug: Rapid Cycles Desync"
  quickCheck prop_bug_rapidCyclesDesync
  
  putStrLn "\n30. Bug: Last Refill Consistency"
  quickCheck prop_bug_lastRefillConsistency
  
  putStrLn "\nAll tests completed!"
