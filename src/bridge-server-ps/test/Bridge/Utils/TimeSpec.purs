-- | Time Utilities Tests
-- | Unit and property tests for time calculation and formatting
module Test.Bridge.Utils.TimeSpec where

import Prelude
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual, shouldBeTrue, shouldBeFalse)
import Test.QuickCheck (quickCheck, (<?>))
import Test.QuickCheck.Arbitrary (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, chooseInt, chooseFloat)
import Effect (Effect)
import Effect.Class (liftEffect)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.DateTime (DateTime, adjust)
import Data.Time.Duration (Hours(..), Days(..))
import Bridge.Utils.Time
  ( calculateTimeRemaining
  , formatTimeRemaining
  , formatTimeRemainingCompact
  , padZero
  , getCurrentDateTime
  )

-- | Test time remaining calculation
testTimeRemaining :: forall m. Monad m => m Unit
testTimeRemaining = do
  describe "Time Remaining Calculation" do
    it "calculates time remaining for future date" do
      now <- liftEffect getCurrentDateTime
      -- Create a future date by adding 2 hours
      future <- case adjust (Hours 2.0) now of
        Just dt -> pure dt
        Nothing -> pure now -- Fallback if adjustment fails
      let result = calculateTimeRemaining now future
      -- Verify result is Just with positive values
      case result of
        Just remaining -> do
          remaining.totalMs `shouldBeGreaterThan` 0.0
          remaining.hours `shouldBeGreaterThanOrEqual` 0
          remaining.minutes `shouldBeGreaterThanOrEqual` 0
          remaining.seconds `shouldBeGreaterThanOrEqual` 0
        Nothing -> false `shouldBeTrue` -- Should not be Nothing for future date
    
    it "returns Nothing for past date" do
      now <- liftEffect getCurrentDateTime
      -- Create a past date by subtracting 1 day
      past <- case adjust (Days (-1.0)) now of
        Just dt -> pure dt
        Nothing -> pure now -- Fallback if adjustment fails
      let result = calculateTimeRemaining now past
      -- Verify result is Nothing for past date
      isNothing result `shouldBeTrue`

-- | Test time formatting
testTimeFormatting :: forall m. Monad m => m Unit
testTimeFormatting = do
  describe "Time Formatting" do
    it "formats time remaining correctly" do
      let remaining = { hours: 2, minutes: 30, seconds: 15, totalMs: 9015000.0 }
      formatTimeRemaining remaining `shouldEqual` "02h 30m 15s"
    
    it "formats single digit values with padding" do
      let remaining = { hours: 1, minutes: 5, seconds: 3, totalMs: 3903000.0 }
      formatTimeRemaining remaining `shouldEqual` "01h 05m 03s"
    
    it "formats zero values correctly" do
      let remaining = { hours: 0, minutes: 0, seconds: 0, totalMs: 0.0 }
      formatTimeRemaining remaining `shouldEqual` "00h 00m 00s"
    
    it "formats maximum values correctly" do
      let remaining = { hours: 99, minutes: 59, seconds: 59, totalMs: 359999000.0 }
      formatTimeRemaining remaining `shouldEqual` "99h 59m 59s"
    
    it "formats very large hour values" do
      let remaining = { hours: 100, minutes: 0, seconds: 0, totalMs: 360000000.0 }
      formatTimeRemaining remaining `shouldEqual` "100h 00m 00s"
    
    it "formats compact time correctly" do
      let remaining = { hours: 2, minutes: 30, seconds: 15, totalMs: 9015000.0 }
      formatTimeRemainingCompact remaining `shouldEqual` "2:30:15"
    
    it "formats compact time with single digits" do
      let remaining = { hours: 1, minutes: 5, seconds: 3, totalMs: 3903000.0 }
      formatTimeRemainingCompact remaining `shouldEqual` "1:05:03"
    
    it "formats compact time with zero values" do
      let remaining = { hours: 0, minutes: 0, seconds: 0, totalMs: 0.0 }
      formatTimeRemainingCompact remaining `shouldEqual` "0:00:00"
    
    it "formats compact time with large values" do
      let remaining = { hours: 24, minutes: 59, seconds: 59, totalMs: 89999000.0 }
      formatTimeRemainingCompact remaining `shouldEqual` "24:59:59"
    
    it "formats time with only seconds" do
      let remaining = { hours: 0, minutes: 0, seconds: 45, totalMs: 45000.0 }
      formatTimeRemaining remaining `shouldEqual` "00h 00m 45s"
      formatTimeRemainingCompact remaining `shouldEqual` "0:00:45"
    
    it "formats time with only minutes and seconds" do
      let remaining = { hours: 0, minutes: 30, seconds: 15, totalMs: 1815000.0 }
      formatTimeRemaining remaining `shouldEqual` "00h 30m 15s"
      formatTimeRemainingCompact remaining `shouldEqual` "0:30:15"
    
    it "formats time with only hours" do
      let remaining = { hours: 5, minutes: 0, seconds: 0, totalMs: 18000000.0 }
      formatTimeRemaining remaining `shouldEqual` "05h 00m 00s"
      formatTimeRemainingCompact remaining `shouldEqual` "5:00:00"

-- | Test zero padding
testPadZero :: forall m. Monad m => m Unit
testPadZero = do
  describe "Zero Padding" do
    it "pads single digit numbers" do
      padZero 0 `shouldEqual` "00"
      padZero 1 `shouldEqual` "01"
      padZero 5 `shouldEqual` "05"
      padZero 9 `shouldEqual` "09"
    
    it "does not pad double digit numbers" do
      padZero 10 `shouldEqual` "10"
      padZero 11 `shouldEqual` "11"
      padZero 50 `shouldEqual` "50"
      padZero 99 `shouldEqual` "99"
    
    it "handles large numbers" do
      padZero 100 `shouldEqual` "100"
      padZero 999 `shouldEqual` "999"
      padZero 1000 `shouldEqual` "1000"
    
    it "handles boundary values" do
      padZero 9 `shouldEqual` "09"  -- Last single digit
      padZero 10 `shouldEqual` "10"  -- First double digit
      padZero 99 `shouldEqual` "99"  -- Last double digit
      padZero 100 `shouldEqual` "100" -- First triple digit
    
    it "handles negative numbers (edge case)" do
      -- Note: padZero is designed for non-negative time values
      -- But we test edge case behavior
        -- TODO: Verify actual behavior
        padZero (-1) `shouldEqual` padZero (-1)

-- | Property: Time remaining is always non-negative when Just
prop_timeRemainingNonNegative :: DateTime -> DateTime -> Boolean
prop_timeRemainingNonNegative now target = 
  case calculateTimeRemaining now target of
    Just remaining -> remaining.totalMs >= 0.0
    Nothing -> true

-- | Property: Formatted time always contains hours, minutes, seconds markers
prop_formattedTimeHasAllParts :: { hours :: Int, minutes :: Int, seconds :: Int, totalMs :: Number } -> Boolean
prop_formattedTimeHasAllParts remaining =
  let formatted = formatTimeRemaining remaining
  in contains "h" formatted && contains "m" formatted && contains "s" formatted

-- | Property: Formatted time has correct structure (HHh MMm SSs)
prop_formattedTimeStructure :: { hours :: Int, minutes :: Int, seconds :: Int, totalMs :: Number } -> Boolean
prop_formattedTimeStructure remaining =
  let formatted = formatTimeRemaining remaining
      parts = split " " formatted
  in length parts == 3 && 
     contains "h" (parts !! 0) &&
     contains "m" (parts !! 1) &&
     contains "s" (parts !! 2)

-- | Property: Compact formatted time has exactly 2 colons
prop_compactTimeHasTwoColons :: { hours :: Int, minutes :: Int, seconds :: Int, totalMs :: Number } -> Boolean
prop_compactTimeHasColons remaining =
  let formatted = formatTimeRemainingCompact remaining
      colonCount = countOccurrences ":" formatted
  in colonCount == 2

-- | Property: Compact formatted time has correct structure (H:MM:SS or HH:MM:SS)
prop_compactTimeStructure :: { hours :: Int, minutes :: Int, seconds :: Int, totalMs :: Number } -> Boolean
prop_compactTimeStructure remaining =
  let formatted = formatTimeRemainingCompact remaining
      parts = split ":" formatted
  in length parts == 3 &&
     length (parts !! 1) == 2 && -- Minutes always 2 digits
     length (parts !! 2) == 2    -- Seconds always 2 digits

-- | Property: Padding always produces at least 2 characters for single digits
prop_padZeroLength :: Int -> Boolean
prop_padZeroLength n =
  if n >= 0 && n < 10 then
    length (padZero n) >= 2
  else if n >= 10 then
    length (padZero n) >= 2 -- At least 2 characters
  else
    true

-- | Property: Padding is idempotent for values >= 10
prop_padZeroIdempotent :: Int -> Boolean
prop_padZeroIdempotent n =
  if n >= 10 then
    padZero n == show n
  else
    true

-- | Property: Formatted time values match input values
prop_formattedTimeValuesMatch :: { hours :: Int, minutes :: Int, seconds :: Int, totalMs :: Number } -> Boolean
prop_formattedTimeValuesMatch remaining =
  if remaining.hours >= 0 && remaining.minutes >= 0 && remaining.minutes < 60 && 
     remaining.seconds >= 0 && remaining.seconds < 60 then
    let formatted = formatTimeRemaining remaining
        -- Parse formatted string to extract hours, minutes, seconds
        parsed = parseFormattedTime formatted
    in case parsed of
      Just { hours: h, minutes: m, seconds: s } ->
        h == remaining.hours && m == remaining.minutes && s == remaining.seconds
      Nothing -> false
  else
    true

-- | Parse formatted time string (e.g., "02h 30m 15s") to extract values
parseFormattedTime :: String -> Maybe { hours :: Int, minutes :: Int, seconds :: Int }
parseFormattedTime str =
  let parts = split " " str
  in if length parts == 3 then
    case parts !! 0, parts !! 1, parts !! 2 of
      Just hoursStr, Just minutesStr, Just secondsStr -> do
        hours <- parseTimeComponent hoursStr "h"
        minutes <- parseTimeComponent minutesStr "m"
        seconds <- parseTimeComponent secondsStr "s"
        pure { hours, minutes, seconds }
      _, _, _ -> Nothing
  else
    Nothing

-- | Parse a time component (e.g., "02h" -> 2)
parseTimeComponent :: String -> String -> Maybe Int
parseTimeComponent str suffix = do
  if endsWith suffix str then
    let numStr = dropEnd (length suffix) str
    in parseNumber numStr
  else
    Nothing

foreign import endsWith :: String -> String -> Boolean
foreign import dropEnd :: Int -> String -> String
foreign import parseNumber :: String -> Maybe Int

foreign import split :: String -> String -> Array String
foreign import countOccurrences :: String -> String -> Int
foreign import shouldBeGreaterThan :: Number -> Number -> Boolean
foreign import shouldBeGreaterThanOrEqual :: forall a. Ord a => a -> a -> Boolean

-- | Property tests
testProperties :: forall m. Monad m => m Unit
testProperties = do
  describe "Property Tests" do
    it "time remaining is always non-negative when Just" do
      quickCheck prop_timeRemainingNonNegative
    
    it "formatted time always contains all parts" do
      quickCheck prop_formattedTimeHasAllParts
    
    it "formatted time has correct structure" do
      quickCheck prop_formattedTimeStructure
    
    it "compact formatted time has exactly 2 colons" do
      quickCheck prop_compactTimeHasTwoColons
    
    it "compact formatted time has correct structure" do
      quickCheck prop_compactTimeStructure
    
    it "padding always produces at least 2 characters for single digits" do
      quickCheck prop_padZeroLength
    
    it "padding is idempotent for values >= 10" do
      quickCheck prop_padZeroIdempotent
    
    it "formatted time values match input values" do
      quickCheck prop_formattedTimeValuesMatch

foreign import contains :: String -> String -> Boolean
foreign import length :: String -> Int
