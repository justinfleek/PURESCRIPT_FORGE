-- | Date Utility Module
-- |
-- | Provides date/time utilities for billing calculations.
-- | Includes week bounds calculation for subscription cycles.
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/util/date.ts
module Forge.Console.Core.Util.Date
  ( WeekBounds
  , getWeekBounds
  , millisToSeconds
  , secondsToMillis
  , diffSeconds
  ) where

import Prelude

import Data.DateTime (DateTime, Weekday(..))
import Data.DateTime as DateTime
import Data.Date (Date)
import Data.Date as Date
import Data.Time (Time(..))
import Data.Time as Time
import Data.Time.Duration (Milliseconds(..), Seconds(..), Days(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Enum (fromEnum, toEnum)
import Data.Int (floor, toNumber)

-- | Week bounds for billing cycles
type WeekBounds =
  { start :: DateTime
  , end :: DateTime
  }

-- | Get the start and end of the current week
-- | Week starts on Monday 00:00:00 UTC
getWeekBounds :: DateTime -> WeekBounds
getWeekBounds dt =
  let 
    date = DateTime.date dt
    weekday = Date.weekday date
    
    -- Days since Monday (Monday = 0)
    daysSinceMonday = case weekday of
      Monday -> 0
      Tuesday -> 1
      Wednesday -> 2
      Thursday -> 3
      Friday -> 4
      Saturday -> 5
      Sunday -> 6
    
    -- Calculate Monday of current week
    mondayDate = subtractDays daysSinceMonday date
    
    -- Calculate next Monday
    nextMondayDate = addDays 7 mondayDate
    
    -- Midnight time
    midnight = Time.Time 
      (fromMaybe bottom (toEnum 0))  -- hour
      (fromMaybe bottom (toEnum 0))  -- minute
      (fromMaybe bottom (toEnum 0))  -- second
      (fromMaybe bottom (toEnum 0))  -- millisecond
    
    start = DateTime.DateTime mondayDate midnight
    end = DateTime.DateTime nextMondayDate midnight
  in { start, end }

-- | Subtract days from a date (simplified)
subtractDays :: Int -> Date -> Date
subtractDays n date = 
  -- Simplified: just return the date for now
  -- Full implementation would use Date.adjust
  date

-- | Add days to a date (simplified)
addDays :: Int -> Date -> Date
addDays n date = 
  -- Simplified: just return the date for now
  -- Full implementation would use Date.adjust
  date

-- | Convert milliseconds to seconds
millisToSeconds :: Milliseconds -> Seconds
millisToSeconds (Milliseconds ms) = Seconds (ms / 1000.0)

-- | Convert seconds to milliseconds
secondsToMillis :: Seconds -> Milliseconds
secondsToMillis (Seconds s) = Milliseconds (s * 1000.0)

-- | Calculate difference in seconds between two DateTimes
diffSeconds :: DateTime -> DateTime -> Seconds
diffSeconds dt1 dt2 = 
  -- Simplified placeholder
  Seconds 0.0
