-- | Time Utilities - Time Calculation and Formatting
-- |
-- | **What:** Provides time calculation and formatting utilities, including countdown timer
-- |         calculations for UTC midnight reset, duration formatting, and DateTime display.
-- | **Why:** Centralizes time-related operations, ensures consistent time formatting across
-- |         the application, and handles UTC midnight calculations for Venice Diem reset.
-- | **How:** Calculates time until UTC midnight, formats durations (hours, minutes, seconds),
-- |         formats DateTime values for display, and computes time differences.
-- |
-- | **Dependencies:**
-- | - `Data.DateTime`: DateTime type and operations
-- | - `Data.Date`: Date type and operations
-- | - `Data.Time`: Time type and operations
-- | - `Sidepanel.FFI.DateTime`: FFI functions for current time and UTC calculations
-- |
-- | **Mathematical Foundation:**
-- | - **UTC Midnight Calculation:** Calculates milliseconds until next UTC midnight (00:00:00).
-- |   Formula: `msUntilMidnight = (nextMidnightUTC - now).totalMs`.
-- | - **Time Remaining:** Breaks down total milliseconds into hours, minutes, seconds:
-- |   - `hours = floor(totalMs / 3600000)`
-- |   - `minutes = floor((totalMs - hours * 3600000) / 60000)`
-- |   - `seconds = floor((totalMs - hours * 3600000 - minutes * 60000) / 1000)`
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Utils.Time as Time
-- |
-- | -- Get time until reset
-- | timeRemaining <- liftEffect Time.getTimeUntilReset
-- | -- { hours: 5, minutes: 30, seconds: 15, totalMs: 19815000.0 }
-- |
-- | -- Format time remaining
-- | Time.formatTimeRemaining timeRemaining  -- "05h 30m 15s"
-- |
-- | -- Format duration
-- | Time.formatDuration startTime endTime  -- "2h 15m" or "45 min"
-- | ```
-- |
-- | Based on spec 52-COUNTDOWN-TIMER.md
module Sidepanel.Utils.Time where

import Prelude
import Data.DateTime (DateTime, diff, date, time)
import Data.Date (Date, canonicalDate, year, month, day)
import Data.Time (Time, midnight, hour, minute)
import Data.Time.Duration (Milliseconds(..))
import Data.Int (toNumber, floor)
import Effect (Effect)

-- | Time remaining until UTC midnight
type TimeRemaining =
  { hours :: Int
  , minutes :: Int
  , seconds :: Int
  , totalMs :: Number
  }

-- | Get time until UTC midnight reset (Effect-based for current time)
-- | Venice Diem resets at 00:00:00 UTC
getTimeUntilReset :: Effect TimeRemaining
getTimeUntilReset = do
  nowMs <- getCurrentTimeMs
  let msUntilReset = calculateMsUntilMidnightUTC nowMs
  let totalMs = msUntilReset
  let totalSeconds = floor (totalMs / 1000.0)
  let hours = floor (toNumber totalSeconds / 3600.0)
  let hoursNum = toNumber hours
  let minutes = floor ((toNumber totalSeconds - (hoursNum * 3600.0)) / 60.0)
  let minutesNum = toNumber minutes
  let seconds = totalSeconds - (hours * 3600) - (minutes * 60)
  pure
    { hours
    , minutes
    , seconds
    , totalMs
    }

-- | Get time until UTC midnight reset (from DateTime - for testing/compatibility)
getTimeUntilResetFromDateTime :: DateTime -> TimeRemaining
getTimeUntilResetFromDateTime now = 
  let midnight = getNextMidnightUTC now
      diffMs = diff midnight now
      totalMs = case diffMs of
        Milliseconds ms -> toNumber ms
      hours = floor (totalMs / 3600000.0)
      hoursNum = toNumber hours
      minutes = floor ((totalMs - (hoursNum * 3600000.0)) / 60000.0)
      minutesNum = toNumber minutes
      seconds = floor ((totalMs - (hoursNum * 3600000.0) - (minutesNum * 60000.0)) / 1000.0)
  in
    { hours
    , minutes
    , seconds
    , totalMs
    }

-- | Get next UTC midnight (from DateTime)
getNextMidnightUTC :: DateTime -> DateTime
getNextMidnightUTC now = 
  let
    -- Get current UTC date/time components
    date = toDate now
    time = toTime now
    year = year date
    month = month date
    day = day date
    
    -- Create DateTime for next midnight UTC
    nextMidnightDate = canonicalDate year month (day + 1)
    nextMidnightTime = Time.midnight
  in
    DateTime nextMidnightDate nextMidnightTime
  where
    import Data.Date (Date, canonicalDate, year, month, day, toDate)
    import Data.Time (Time, midnight, toTime)

-- | Import FFI functions
import Sidepanel.FFI.DateTime (calculateMsUntilMidnightUTC, getCurrentTimeMs)

-- | Format time remaining as string
formatTimeRemaining :: TimeRemaining -> String
formatTimeRemaining { hours, minutes, seconds } =
  pad hours <> "h " <> pad minutes <> "m " <> pad seconds <> "s"
  where
    pad n = if n < 10 then "0" <> show n else show n

-- | Format time remaining compact
formatTimeRemainingCompact :: TimeRemaining -> String
formatTimeRemainingCompact { hours, minutes, seconds } =
  show hours <> ":" <> pad minutes <> ":" <> pad seconds
  where
    pad n = if n < 10 then "0" <> show n else show n

-- | Format DateTime as time string (e.g., "2:34 PM")
formatTime :: DateTime -> String
formatTime dt =
  let
    h = hour (time dt)
    m = minute (time dt)
    h12 = if h == 0 then 12 else if h > 12 then h - 12 else h
    ampm = if h < 12 then "AM" else "PM"
  in
    show h12 <> ":" <> pad m <> " " <> ampm
  where
    pad n = if n < 10 then "0" <> show n else show n

-- | Format DateTime as date and time string
formatDateTime :: DateTime -> String
formatDateTime dt =
  let
    d = date dt
    monthName = show (month d)
    dayNum = day d
    yr = year d
    timeStr = formatTime dt
  in
    monthName <> " " <> show dayNum <> ", " <> show yr <> " " <> timeStr

-- | Format duration between two DateTimes
formatDuration :: DateTime -> DateTime -> String
formatDuration start end =
  let
    diffMs = diff end start
    totalMs = case diffMs of
      Milliseconds ms -> toNumber ms
    totalMinutes = floor (totalMs / 60000.0)
    hours = floor (toNumber totalMinutes / 60.0)
    minutes = totalMinutes - (hours * 60)
  in
    if hours > 0
      then show hours <> "h " <> show minutes <> "m"
      else show minutes <> " min"
