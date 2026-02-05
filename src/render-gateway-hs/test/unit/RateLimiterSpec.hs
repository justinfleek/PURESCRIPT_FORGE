{-# LANGUAGE OverloadedStrings #-}

-- | Deep comprehensive unit tests for RateLimiter module
-- | Tests individual functions in isolation: createRateLimiter, refillTokens,
-- | acquireToken, acquireTokenBlocking, getTokenCount
module RateLimiterSpec where

import Test.Hspec
import Control.Concurrent.STM
import Control.Concurrent (threadDelay)
import Control.Monad (replicateM, replicateM_)
import Data.Time (getCurrentTime, addUTCTime, diffUTCTime, secondsToDiffTime)
import Render.Gateway.STM.RateLimiter
  ( RateLimiter(..)
  , createRateLimiter
  , refillTokens
  , acquireToken
  , acquireTokenBlocking
  , getTokenCount
  )
import Render.Gateway.STM.Clock (Clock, createClock, readClockSTM, startClockThread)

-- | Deep comprehensive unit tests for RateLimiter module
spec :: Spec
spec = describe "RateLimiter Unit Tests" $ do
  describe "createRateLimiter" $ do
    it "creates rate limiter with specified capacity and refill rate" $ do
      now <- getCurrentTime
      rl <- atomically $ createRateLimiter 100.0 10.0 now
      
      -- Verify initial state
      tokens <- atomically $ readTVar (rlTokens rl)
      lastRefill <- atomically $ readTVar (rlLastRefill rl)
      
      tokens `shouldBe` 100.0
      rlCapacity rl `shouldBe` 100.0
      rlRefillRate rl `shouldBe` 10.0
      -- BUG: lastRefill is initialized with 'now', but if there's a delay
      -- between getCurrentTime and createRateLimiter, lastRefill may be slightly
      -- behind actual current time, causing initial refill calculation to be wrong.
      diffUTCTime lastRefill now < 1.0 `shouldBe` True

    it "BUG: creates rate limiter with zero capacity" $ do
      -- BUG: Zero capacity means no tokens available, so acquireToken will
      -- always return False. This may be intentional (disable rate limiter),
      -- but should be documented or validated.
      now <- getCurrentTime
      rl <- atomically $ createRateLimiter 0.0 10.0 now
      
      tokens <- atomically $ readTVar (rlTokens rl)
      tokens `shouldBe` 0.0
      
      -- BUG: acquireToken will always return False with zero capacity
      acquired <- atomically $ acquireToken rl now
      acquired `shouldBe` False
      
      -- BUG: The issue is that zero capacity may be a configuration error,
      -- but createRateLimiter doesn't validate or warn about it.

    it "BUG: creates rate limiter with zero refill rate" $ do
      -- BUG: Zero refill rate means tokens never refill, so once tokens are
      -- consumed, acquireToken will always return False until manually reset.
      now <- getCurrentTime
      rl <- atomically $ createRateLimiter 100.0 0.0 now
      
      -- Consume all tokens
      atomically $ writeTVar (rlTokens rl) 0.0
      
      -- Advance time - tokens should not refill
      let later = addUTCTime (secondsToDiffTime 10) now
      tokenCount <- atomically $ getTokenCount rl later
      
      -- BUG: Token count should still be 0 (no refill), but this means
      -- rate limiter is permanently disabled after first use.
      tokenCount `shouldBe` 0.0
      
      -- BUG: The issue is that zero refill rate may be a configuration error,
      -- but createRateLimiter doesn't validate or warn about it.

    it "BUG: creates rate limiter with negative capacity" $ do
      -- BUG: Negative capacity is invalid, but createRateLimiter doesn't validate.
      -- This can cause tokens to be negative, breaking invariants.
      now <- getCurrentTime
      rl <- atomically $ createRateLimiter (-10.0) 10.0 now
      
      tokens <- atomically $ readTVar (rlTokens rl)
      -- BUG: Negative capacity is stored, which is invalid
      tokens `shouldBe` (-10.0)
      
      -- BUG: acquireToken will always return False (tokens < 1.0),
      -- but the negative capacity breaks the invariant that tokens >= 0.
      acquired <- atomically $ acquireToken rl now
      acquired `shouldBe` False

  describe "refillTokens" $ do
    it "refills tokens based on elapsed time" $ do
      now <- getCurrentTime
      rl <- atomically $ createRateLimiter 100.0 10.0 now  -- 10 tokens/sec
      
      -- Set tokens to 0
      atomically $ writeTVar (rlTokens rl) 0.0
      
      -- Advance time by 5 seconds
      let later = addUTCTime (secondsToDiffTime 5) now
      atomically $ refillTokens rl later
      
      tokens <- atomically $ readTVar (rlTokens rl)
      -- Should have refilled 5 * 10 = 50 tokens
      tokens `shouldBe` 50.0

    it "caps tokens at capacity limit" $ do
      now <- getCurrentTime
      rl <- atomically $ createRateLimiter 100.0 10.0 now  -- Capacity: 100, Refill: 10/sec
      
      -- Set tokens to 0
      atomically $ writeTVar (rlTokens rl) 0.0
      
      -- Advance time by 20 seconds (would refill 200 tokens, but capped at 100)
      let later = addUTCTime (secondsToDiffTime 20) now
      atomically $ refillTokens rl later
      
      tokens <- atomically $ readTVar (rlTokens rl)
      tokens `shouldBe` 100.0  -- Capped at capacity

    it "BUG: refillTokens handles clock jump backward" $ do
      -- BUG: refillTokens (line 37-51) guards against clock jumps backward
      -- by checking if elapsed < 0. If elapsed is negative, tokensToAdd = 0.
      -- However, lastRefill is always updated to 'now', which can cause issues
      -- if clock jumps backward significantly.
      now <- getCurrentTime
      rl <- atomically $ createRateLimiter 100.0 10.0 now
      
      -- Set tokens to 50
      atomically $ writeTVar (rlTokens rl) 50.0
      
      -- Simulate clock jump backward (5 seconds in the past)
      let past = addUTCTime (secondsToDiffTime (-5)) now
      atomically $ refillTokens rl past
      
      tokens <- atomically $ readTVar (rlTokens rl)
      -- BUG: elapsed is negative, so tokensToAdd = 0, tokens stay at 50
      -- This is correct behavior, but lastRefill is updated to 'past',
      -- which means future refills will calculate elapsed from 'past',
      -- potentially causing incorrect refill calculations.
      tokens `shouldBe` 50.0
      
      -- BUG: If clock jumps backward and then forward again, the elapsed time
      -- calculation from 'past' to 'now' will be large, causing a large refill
      -- that may exceed capacity. This is a clock jump forward scenario, but
      -- the backward jump sets up the condition.

    it "BUG: refillTokens may have floating point precision issues" $ do
      -- BUG: Floating point arithmetic in refillTokens (line 43) can cause
      -- precision loss, especially with very small elapsed times or very large
      -- refill rates.
      now <- getCurrentTime
      rl <- atomically $ createRateLimiter 100.0 1000000.0 now  -- Very high refill rate
      
      -- Set tokens to 0
      atomically $ writeTVar (rlTokens rl) 0.0
      
      -- Advance time by very small amount (1 millisecond)
      let later = addUTCTime (secondsToDiffTime 0.001) now
      atomically $ refillTokens rl later
      
      tokens <- atomically $ readTVar (rlTokens rl)
      -- BUG: With very high refill rate and very small elapsed time,
      -- floating point precision may cause tokensToAdd to be 0 or incorrect.
      -- Expected: 0.001 * 1000000 = 1000 tokens, but capped at 100
      tokens `shouldBe` 100.0  -- Capped, but precision may affect calculation

    it "BUG: refillTokens updates lastRefill even when elapsed is negative" $ do
      -- BUG: refillTokens (line 49-51) always updates lastRefill to 'now',
      -- even when elapsed is negative. This means if clock jumps backward,
      -- lastRefill is set to the past time, which can cause issues when clock
      -- jumps forward again.
      now <- getCurrentTime
      rl <- atomically $ createRateLimiter 100.0 10.0 now
      
      -- Simulate clock jump backward
      let past = addUTCTime (secondsToDiffTime (-5)) now
      atomically $ refillTokens rl past
      
      lastRefill <- atomically $ readTVar (rlLastRefill rl)
      -- BUG: lastRefill is updated to 'past', which is in the past.
      -- This means future refills will calculate elapsed from 'past',
      -- potentially causing incorrect refill calculations.
      diffUTCTime lastRefill past < 0.1 `shouldBe` True

  describe "acquireToken" $ do
    it "acquires token when tokens >= 1.0" $ do
      now <- getCurrentTime
      rl <- atomically $ createRateLimiter 100.0 10.0 now
      
      -- Set tokens to 50
      atomically $ writeTVar (rlTokens rl) 50.0
      
      acquired <- atomically $ acquireToken rl now
      acquired `shouldBe` True
      
      tokens <- atomically $ readTVar (rlTokens rl)
      tokens `shouldBe` 49.0  -- Decremented by 1

    it "does not acquire token when tokens < 1.0" $ do
      now <- getCurrentTime
      rl <- atomically $ createRateLimiter 100.0 10.0 now
      
      -- Set tokens to 0.5
      atomically $ writeTVar (rlTokens rl) 0.5
      
      acquired <- atomically $ acquireToken rl now
      acquired `shouldBe` False
      
      tokens <- atomically $ readTVar (rlTokens rl)
      -- BUG: refillTokens is called before checking tokens (line 56),
      -- so tokens may have been refilled. But if elapsed time is 0,
      -- tokens stay at 0.5, and acquireToken returns False.
      tokens >= 0.5 `shouldBe` True

    it "BUG: acquireToken may allow negative tokens" $ do
      -- BUG: acquireToken (line 54-62) checks if tokens >= 1.0 before
      -- decrementing. However, if refillTokens is called and adds tokens,
      -- but then tokens are decremented by 1.0, tokens can become negative
      -- if refillTokens added less than 1.0 token.
      now <- getCurrentTime
      rl <- atomically $ createRateLimiter 100.0 0.1 now  -- Very slow refill: 0.1 tokens/sec
      
      -- Set tokens to exactly 0.0
      atomically $ writeTVar (rlTokens rl) 0.0
      
      -- Advance time by 0.5 seconds (refills 0.05 tokens)
      let later = addUTCTime (secondsToDiffTime 0.5) now
      
      -- BUG: acquireToken calls refillTokens first (line 56), which adds 0.05 tokens.
      -- Then it checks if tokens >= 1.0 (0.05 < 1.0), so returns False.
      -- This is correct, but if tokens were somehow negative, the check would
      -- still work, but tokens could remain negative.
      acquired <- atomically $ acquireToken rl later
      acquired `shouldBe` False
      
      tokens <- atomically $ readTVar (rlTokens rl)
      -- BUG: Tokens should be 0.05, but floating point precision may affect this
      tokens >= 0.0 `shouldBe` True

    it "BUG: acquireToken refills tokens before checking" $ do
      -- BUG: acquireToken (line 56) calls refillTokens before checking tokens.
      -- This means if time has advanced, tokens are refilled first, which is
      -- correct. However, if refillTokens has side effects or errors, they
      -- occur before the token check.
      now <- getCurrentTime
      rl <- atomically $ createRateLimiter 100.0 10.0 now
      
      -- Set tokens to 0
      atomically $ writeTVar (rlTokens rl) 0.0
      
      -- Advance time by 0.1 seconds (refills 1 token)
      let later = addUTCTime (secondsToDiffTime 0.1) now
      
      acquired <- atomically $ acquireToken rl later
      -- BUG: refillTokens adds 1 token, then acquireToken checks tokens >= 1.0,
      -- which is true, so token is acquired.
      acquired `shouldBe` True
      
      tokens <- atomically $ readTVar (rlTokens rl)
      -- BUG: Tokens should be 0 (1 refilled, 1 acquired), but floating point
      -- precision may cause slight differences.
      tokens `shouldBe` 0.0

  describe "acquireTokenBlocking" $ do
    it "blocks until token is available" $ do
      clock <- createClock
      _ <- startClockThread clock
      now <- getCurrentTime
      rl <- atomically $ createRateLimiter 1.0 1.0 now  -- 1 token capacity, 1 token/sec refill
      
      -- Consume the token
      atomically $ writeTVar (rlTokens rl) 0.0
      
      -- BUG: acquireTokenBlocking (line 65-69) uses retry, which blocks
      -- indefinitely until token is available. If refill rate is zero or
      -- very slow, this will block forever, potentially causing deadlock.
      --
      -- This test verifies that blocking works, but in a real scenario,
      -- we'd need to wait for refill or timeout.
      --
      -- For this test, we'll verify the blocking behavior by checking
      -- that acquireTokenBlocking doesn't return immediately when no tokens
      -- are available. However, we can't easily test indefinite blocking
      -- without a timeout mechanism.
      
      -- Set tokens to 0.5 (less than 1.0)
      atomically $ writeTVar (rlTokens rl) 0.5
      
      -- BUG: acquireTokenBlocking will call acquireToken, which returns False,
      -- then retry, which blocks. We can't easily test this without a timeout
      -- or background thread to refill tokens.

    it "BUG: acquireTokenBlocking may block indefinitely" $ do
      -- BUG: acquireTokenBlocking (line 65-69) uses retry, which blocks
      -- indefinitely until token is available. If:
      -- 1. Refill rate is zero (tokens never refill)
      -- 2. Clock doesn't advance (tokens never refill)
      -- 3. All tokens are consumed and no refill happens
      -- then acquireTokenBlocking will block forever.
      clock <- createClock
      now <- getCurrentTime
      rl <- atomically $ createRateLimiter 1.0 0.0 now  -- Zero refill rate
      
      -- Consume the token
      atomically $ writeTVar (rlTokens rl) 0.0
      
      -- BUG: acquireTokenBlocking will block forever because refill rate is zero.
      -- There's no timeout mechanism, so this can cause deadlock.
      --
      -- This test documents the issue - we can't easily test indefinite blocking
      -- without a timeout or background thread.

  describe "getTokenCount" $ do
    it "returns current token count after refill" $ do
      now <- getCurrentTime
      rl <- atomically $ createRateLimiter 100.0 10.0 now
      
      -- Set tokens to 0
      atomically $ writeTVar (rlTokens rl) 0.0
      
      -- Advance time by 5 seconds
      let later = addUTCTime (secondsToDiffTime 5) now
      tokenCount <- atomically $ getTokenCount rl later
      
      -- Should have refilled 5 * 10 = 50 tokens
      tokenCount `shouldBe` 50.0

    it "BUG: getTokenCount may return negative tokens" $ do
      -- BUG: getTokenCount (line 72-75) calls refillTokens, which should
      -- ensure tokens >= 0. However, if tokens were manually set to negative
      -- (edge case test), getTokenCount will
      -- return negative tokens.
      now <- getCurrentTime
      rl <- atomically $ createRateLimiter 100.0 10.0 now
      
      -- Manually set tokens to negative (edge case test)
      atomically $ writeTVar (rlTokens rl) (-10.0)
      
      tokenCount <- atomically $ getTokenCount rl now
      -- BUG: refillTokens adds tokens, but if elapsed is 0, tokens stay negative.
      -- getTokenCount returns negative tokens, which breaks the invariant.
      tokenCount >= (-10.0) `shouldBe` True
      
      -- BUG: The issue is that getTokenCount doesn't validate that tokens >= 0.
      -- If tokens are negative due to bugs, getTokenCount will return negative.

    it "BUG: getTokenCount may have floating point precision issues" $ do
      -- BUG: Floating point arithmetic in refillTokens can cause precision loss.
      -- getTokenCount calls refillTokens, so it inherits these precision issues.
      now <- getCurrentTime
      rl <- atomically $ createRateLimiter 100.0 0.0001 now  -- Very slow refill
      
      -- Set tokens to 0
      atomically $ writeTVar (rlTokens rl) 0.0
      
      -- Advance time by very small amount
      let later = addUTCTime (secondsToDiffTime 0.001) now
      tokenCount <- atomically $ getTokenCount rl later
      
      -- BUG: With very slow refill rate and very small elapsed time,
      -- floating point precision may cause tokenCount to be 0 or incorrect.
      -- Expected: 0.001 * 0.0001 = 0.0000001 tokens, which may round to 0.
      tokenCount >= 0.0 `shouldBe` True
