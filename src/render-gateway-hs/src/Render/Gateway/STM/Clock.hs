{-# LANGUAGE StrictData #-}

-- | Render Gateway Clock TVar Pattern
-- | Time-dependent STM operations require a clock TVar updated by background thread
module Render.Gateway.STM.Clock where

import Prelude hiding (head, tail)
import Control.Concurrent (forkIO, threadDelay, ThreadId)
import Control.Concurrent.STM
import Data.Time (UTCTime, getCurrentTime, toRational)
import Data.Time.Clock.POSIX (utcTimeToPOSIXSeconds)

-- | Clock with POSIX and UTC time
data Clock = Clock
  { clockPosix :: TVar Double -- POSIX timestamp
  , clockUTC :: TVar UTCTime -- UTC time
  }

-- | Create clock
-- | Note: Clock must be initialized with updateClock before use
createClock :: IO Clock
createClock = do
  -- Initialize with current time immediately
  now <- getCurrentTime
  let posix = realToFrac (utcTimeToPOSIXSeconds now)
  atomically $ do
    posixVar <- newTVar posix
    utcVar <- newTVar now
    pure Clock
      { clockPosix = posixVar
      , clockUTC = utcVar
      }

-- | Read clock in STM transaction
readClockSTM :: Clock -> STM (Double, UTCTime)
readClockSTM Clock {..} = do
  posix <- readTVar clockPosix
  utc <- readTVar clockUTC
  pure (posix, utc)

-- | Update clock (called by background thread every 100ms)
updateClock :: Clock -> IO ()
updateClock Clock {..} = do
  now <- getCurrentTime
  let posix = realToFrac (utcTimeToPOSIXSeconds now)
  atomically $ do
    writeTVar clockPosix posix
    writeTVar clockUTC now

-- | Start clock update thread
startClockThread :: Clock -> IO ThreadId
startClockThread clock = forkIO $ clockLoop clock
  where
    clockLoop c = do
      updateClock c
      threadDelay 100000 -- 100ms
      clockLoop c
