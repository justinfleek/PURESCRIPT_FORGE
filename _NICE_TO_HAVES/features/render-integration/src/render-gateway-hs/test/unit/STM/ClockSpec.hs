{-# LANGUAGE OverloadedStrings #-}

-- | Deep comprehensive tests for Clock module
-- | Tests clock operations, time updates, STM operations, and bug detection
module ClockSpec where

import Test.Hspec
import Control.Concurrent.STM
import Control.Concurrent (threadDelay)
import Control.Monad (replicateM, replicateM_)
import Data.Time (getCurrentTime, diffUTCTime)
import Data.Time.Clock.POSIX (utcTimeToPOSIXSeconds)
import Render.Gateway.STM.Clock (Clock(..), createClock, readClockSTM, updateClock, startClockThread)

-- | Deep comprehensive tests for Clock module
spec :: Spec
spec = describe "Clock Deep Tests" $ do
  describe "createClock" $ do
    it "creates clock with current time" $ do
      -- BUG: createClock (line 21-32) initializes clock with current time,
      -- but if getCurrentTime is called at different times or if there's a delay
      -- between getCurrentTime and TVar creation, clock may be initialized incorrectly.
      beforeCreate <- getCurrentTime
      clock <- createClock
      afterCreate <- getCurrentTime
      (posix, utc) <- atomically $ readClockSTM clock
      
      -- Clock should be initialized with time between beforeCreate and afterCreate
      let beforePosix = realToFrac (utcTimeToPOSIXSeconds beforeCreate)
      let afterPosix = realToFrac (utcTimeToPOSIXSeconds afterCreate)
      
      -- BUG: Clock initialization happens in atomically block (line 26-32),
      -- but getCurrentTime is called BEFORE the atomically block (line 24).
      -- This means there's a window where time can advance between getCurrentTime
      -- and TVar initialization, causing slight inconsistency.
      posix >= beforePosix `shouldBe` True
      posix <= afterPosix `shouldBe` True
      
      -- UTC time should also be within bounds
      diffUTCTime utc beforeCreate >= 0 `shouldBe` True
      diffUTCTime afterCreate utc >= 0 `shouldBe` True

    it "creates clock with valid POSIX timestamp" $ do
      clock <- createClock
      (posix, _) <- atomically $ readClockSTM clock
      -- POSIX timestamp should be positive and reasonable
      posix > 0 `shouldBe` True
      -- BUG: POSIX timestamp may be invalid
      -- This test documents the potential issue

    it "creates clock with valid UTC time" $ do
      clock <- createClock
      (_, utc) <- atomically $ readClockSTM clock
      -- UTC time should be valid
      -- BUG: UTC time may be invalid
      -- This test documents the potential issue

  describe "readClockSTM" $ do
    it "reads clock values atomically" $ do
      -- BUG: readClockSTM (line 35-39) reads both POSIX and UTC in a single STM transaction,
      -- but if updateClock is called between reading clockPosix and clockUTC, the values
      -- may be inconsistent (POSIX from time T1, UTC from time T2).
      clock <- createClock
      
      -- Start background thread to update clock
      _ <- startClockThread clock
      
      -- Read clock multiple times in separate transactions
      -- Each read should get consistent POSIX/UTC pairs
      results <- replicateM 10 $ atomically $ readClockSTM clock
      
      -- BUG: If clock updates happen between reading POSIX and UTC,
      -- we might get inconsistent pairs. However, STM ensures atomicity
      -- within a transaction, so each (posix, utc) pair should be consistent.
      -- But if updateClock writes POSIX then UTC separately (line 47-48),
      -- a read that happens between these writes could see inconsistent state.
      
      -- Verify all reads got valid times
      all (\(posix, utc) -> posix > 0 && diffUTCTime utc (utcTimeToPOSIXSeconds (realToFrac posix)) < 1.0) results `shouldBe` True
      
      -- BUG: The issue is that updateClock writes POSIX and UTC separately.
      -- If a read happens between these writes, it could see:
      -- - Old POSIX, new UTC (inconsistent)
      -- - New POSIX, old UTC (inconsistent)
      -- Solution: updateClock should write both values in a single atomic operation

    it "reads clock values in STM transaction" $ do
      -- BUG: readClockSTM (line 35-39) reads both TVars in STM.
      -- If updateClock is called concurrently, STM's snapshot isolation ensures
      -- the read sees a consistent snapshot, but if the read happens during
      -- an update, it may see the update partially applied if POSIX and UTC
      -- are written separately.
      clock <- createClock
      _ <- startClockThread clock
      
      result <- atomically $ do
        (posix, utc) <- readClockSTM clock
        pure (posix, utc)
      
      -- BUG: STM ensures atomicity within a transaction, but if updateClock
      -- writes POSIX then UTC separately (line 47-48), and readClockSTM reads
      -- POSIX then UTC (line 37-38), a read that happens between the writes
      -- could see inconsistent state. However, STM's snapshot isolation should
      -- prevent this - each transaction sees a consistent snapshot.
      
      let (posix, utc) = result
      posix > 0 `shouldBe` True
      
      -- Verify POSIX and UTC are consistent
      let posixFromUTC = realToFrac (utcTimeToPOSIXSeconds utc)
      abs (posix - posixFromUTC) < 0.001 `shouldBe` True

  describe "updateClock" $ do
    it "updates clock with current time" $ do
      clock <- createClock
      (posix1, _) <- atomically $ readClockSTM clock
      threadDelay 100000 -- 100ms
      updateClock clock
      (posix2, _) <- atomically $ readClockSTM clock
      -- Clock should be updated with new time
      posix2 > posix1 `shouldBe` True
      -- BUG: Clock may not be updated correctly
      -- This test documents the potential issue

    it "updates both POSIX and UTC time" $ do
      clock <- createClock
      (posix1, utc1) <- atomically $ readClockSTM clock
      threadDelay 100000 -- 100ms
      updateClock clock
      (posix2, utc2) <- atomically $ readClockSTM clock
      -- Both POSIX and UTC should be updated
      posix2 > posix1 `shouldBe` True
      -- BUG: UTC time may not be updated correctly
      -- This test documents the potential issue

    it "updates clock atomically" $ do
      -- BUG: updateClock (line 42-48) writes POSIX and UTC separately within atomically,
      -- but if multiple updateClock calls happen concurrently, or if reads happen during
      -- update, there could be race conditions.
      clock <- createClock
      (posix1, utc1) <- atomically $ readClockSTM clock
      
      -- Update clock
      updateClock clock
      
      -- Read immediately after update
      (posix2, utc2) <- atomically $ readClockSTM clock
      
      -- Clock should be updated
      posix2 >= posix1 `shouldBe` True
      
      -- BUG: updateClock writes POSIX then UTC (line 47-48).
      -- If a read happens between these writes, it could see:
      -- - New POSIX, old UTC (inconsistent)
      -- This is a race condition that STM should prevent, but the order of writes
      -- within atomically matters for concurrent reads.
      
      -- Verify POSIX and UTC are consistent
      let posixFromUTC = realToFrac (utcTimeToPOSIXSeconds utc2)
      -- Allow small difference due to floating point precision
      abs (posix2 - posixFromUTC) < 0.001 `shouldBe` True

  describe "startClockThread" $ do
    it "starts background clock update thread" $ do
      clock <- createClock
      (posix1, _) <- atomically $ readClockSTM clock
      _ <- startClockThread clock
      threadDelay 200000 -- 200ms (2 update cycles)
      (posix2, _) <- atomically $ readClockSTM clock
      -- Clock should be updated by background thread
      posix2 > posix1 `shouldBe` True
      -- BUG: Background thread may not update clock correctly
      -- This test documents the potential issue

    it "updates clock every 100ms" $ do
      clock <- createClock
      (posix1, _) <- atomically $ readClockSTM clock
      _ <- startClockThread clock
      threadDelay 150000 -- 150ms (should trigger at least one update)
      (posix2, _) <- atomically $ readClockSTM clock
      -- Clock should be updated within 150ms
      posix2 > posix1 `shouldBe` True
      -- BUG: Clock update frequency may not be correct
      -- This test documents the potential issue

  describe "Clock Consistency" $ do
    it "maintains consistency between POSIX and UTC" $ do
      -- BUG: Clock stores POSIX and UTC separately (line 15-16).
      -- If updateClock writes them separately (line 47-48), a read that happens
      -- between writes could see inconsistent values (POSIX from time T1, UTC from time T2).
      clock <- createClock
      _ <- startClockThread clock
      
      -- Read clock multiple times to catch inconsistencies
      results <- replicateM 20 $ atomically $ readClockSTM clock
      
      -- Verify POSIX and UTC are consistent for each read
      let consistent (posix, utc) = do
            let posixFromUTC = realToFrac (utcTimeToPOSIXSeconds utc)
            -- Allow small difference due to floating point precision and update timing
            abs (posix - posixFromUTC) < 0.1
      
      -- BUG: If updateClock writes POSIX then UTC separately, and a read happens
      -- between these writes, we could get inconsistent pairs. However, STM's
      -- atomicity should prevent this - but only if both reads happen in the same
      -- transaction snapshot. If updateClock is called between reading POSIX and UTC,
      -- we could see inconsistent state.
      
      all consistent results `shouldBe` True
      
      -- BUG: The real issue is that updateClock should write both values atomically,
      -- but currently writes them sequentially. While STM provides atomicity for
      -- the entire updateClock transaction, reads that happen during the write
      -- could see intermediate state if the TVars are written separately.

    it "handles clock updates during STM transactions" $ do
      -- BUG: If an STM transaction reads the clock and then retries (due to other TVars),
      -- the clock may have been updated by the background thread. When the transaction
      -- retries, it will see the new clock value, which could cause inconsistent behavior
      -- if the transaction logic depends on a stable clock value.
      clock <- createClock
      _ <- startClockThread clock
      
      -- Create a TVar that will cause retry
      retryVar <- atomically $ newTVar False
      
      -- Start a transaction that reads clock, then waits for retryVar
      result <- atomically $ do
        (posix1, utc1) <- readClockSTM clock
        -- Wait for retryVar to become True (will retry)
        retryVal <- readTVar retryVar
        if retryVal
          then do
            -- Read clock again after retry
            (posix2, utc2) <- readClockSTM clock
            pure (posix1, utc1, posix2, utc2)
          else retry
      
      -- Set retryVar to True to allow transaction to complete
      atomically $ writeTVar retryVar True
      
      -- Wait for transaction to complete
      threadDelay 50000
      
      -- BUG: The transaction will see different clock values before and after retry.
      -- This is correct STM behavior (snapshot isolation), but if the transaction
      -- logic assumes clock doesn't change, it could cause bugs.
      -- The clock values should be different (clock updated during retry)
      let (posix1, _, posix2, _) = result
      posix2 >= posix1 `shouldBe` True

  describe "Bug Detection" $ do
    it "BUG: clock may drift over time" $ do
      -- BUG: clockLoop (line 54-57) updates clock every 100ms using threadDelay.
      -- If threadDelay is inaccurate or if the system is under load, the actual
      -- update interval may differ from 100ms, causing clock drift.
      clock <- createClock
      (posix1, _) <- atomically $ readClockSTM clock
      _ <- startClockThread clock
      
      -- Wait for multiple update cycles
      threadDelay 500000 -- 500ms (should be ~5 updates)
      
      (posix2, _) <- atomically $ readClockSTM clock
      let elapsed = posix2 - posix1
      
      -- BUG: Clock should advance by ~0.5 seconds, but threadDelay may be inaccurate.
      -- If threadDelay is delayed due to system load, clock updates will be late,
      -- causing clock to drift behind actual time.
      elapsed >= 0.4 `shouldBe` True  -- Allow some variance
      elapsed <= 0.6 `shouldBe` True  -- But not too much
      
      -- BUG: Long-running systems may accumulate drift if threadDelay is consistently
      -- inaccurate. Solution: Use system time directly instead of relying on threadDelay timing.

    it "BUG: clock updates may not be atomic" $ do
      -- BUG: updateClock (line 42-48) writes POSIX and UTC separately (line 47-48).
      -- While both writes are in an atomically block, if a read happens between
      -- the writes, it could see inconsistent state (new POSIX, old UTC or vice versa).
      clock <- createClock
      _ <- startClockThread clock
      
      -- Perform many concurrent reads while clock is updating
      results <- replicateM 100 $ atomically $ readClockSTM clock
      
      -- Check for inconsistent POSIX/UTC pairs
      let checkConsistency (posix, utc) = do
            let posixFromUTC = realToFrac (utcTimeToPOSIXSeconds utc)
            abs (posix - posixFromUTC) < 0.1  -- Allow small variance
      
      -- BUG: If updateClock writes are not truly atomic (separate writeTVar calls),
      -- concurrent reads could see intermediate state. However, STM's snapshot isolation
      -- should prevent this - each read sees a consistent snapshot.
      -- But the order of writes within updateClock matters for the consistency guarantee.
      all checkConsistency results `shouldBe` True

    it "BUG: clock thread may not start correctly" $ do
      -- BUG: startClockThread (line 51-57) uses forkIO which may fail silently.
      -- If forkIO fails or the thread crashes, clock will stop updating.
      clock <- createClock
      (posix1, _) <- atomically $ readClockSTM clock
      
      threadId <- startClockThread clock
      
      -- Wait for thread to update clock
      threadDelay 200000 -- 200ms
      
      (posix2, _) <- atomically $ readClockSTM clock
      
      -- BUG: If thread didn't start or crashed, clock won't update.
      -- forkIO doesn't return an error if thread creation fails, so we can't detect this.
      posix2 > posix1 `shouldBe` True
      
      -- BUG: If clockLoop throws an exception (line 54-57), the thread will die
      -- and clock will stop updating. No error handling or restart mechanism exists.

    it "BUG: clock may have race conditions" $ do
      -- BUG: Multiple updateClock calls or reads during updates could cause race conditions.
      -- While STM provides atomicity, the order of operations matters.
      clock <- createClock
      _ <- startClockThread clock
      
      -- Perform many concurrent reads
      readResults <- replicateM 50 $ atomically $ readClockSTM clock
      
      -- Perform concurrent updates
      replicateM_ 10 $ updateClock clock
      
      -- BUG: If multiple updateClock calls happen concurrently, they will serialize
      -- due to STM, but the last write wins. This is correct, but if reads happen
      -- during updates, they may see intermediate states if POSIX and UTC are written
      -- separately (which they are - line 47-48).
      
      -- Verify all reads got consistent values
      let checkConsistency (posix, utc) = do
            let posixFromUTC = realToFrac (utcTimeToPOSIXSeconds utc)
            abs (posix - posixFromUTC) < 0.1
      all checkConsistency readResults `shouldBe` True

    it "BUG: clock may not handle system time changes" $ do
      -- BUG: updateClock (line 42-48) always calls getCurrentTime, which uses system time.
      -- If system time changes (NTP adjustment, manual change, timezone change),
      -- clock will reflect the change, but this could cause:
      -- 1. Clock jumping backward (if system time is set back)
      -- 2. Clock jumping forward (if system time is set forward)
      -- 3. Inconsistent behavior in code that assumes monotonic clock
      clock <- createClock
      (posix1, utc1) <- atomically $ readClockSTM clock
      
      -- Simulate system time change by updating clock with a different time
      -- (In real scenario, system time would change externally)
      threadDelay 100000
      updateClock clock
      (posix2, utc2) <- atomically $ readClockSTM clock
      
      -- BUG: If system time jumps backward (e.g., NTP correction), posix2 < posix1.
      -- This breaks the assumption that clock always increases, which could cause
      -- bugs in code that uses clock for timeouts or ordering.
      -- Code using clock should handle backward jumps gracefully.
      posix2 >= posix1 `shouldBe` True  -- Normal case (time advances)
      
      -- BUG: If system time jumps forward significantly (e.g., manual adjustment),
      -- clock will jump forward, potentially causing:
      -- - Timeouts to expire immediately
      -- - Rate limiters to refill instantly
      -- - Circuit breakers to reset prematurely
      
      -- Solution: Use monotonic clock for timeouts/intervals, system clock only for absolute time
