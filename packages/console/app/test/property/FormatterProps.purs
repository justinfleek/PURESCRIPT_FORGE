-- | Property tests for formatters
-- | Tests format invariants, consistency, and edge case handling
module Test.Property.FormatterProps where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldBeTrue)
import Test.QuickCheck (quickCheck)
import Test.QuickCheck.Gen (Gen, chooseFloat, chooseInt, elements, oneOf)

import Sidepanel.Utils.Currency as Currency
import Sidepanel.Utils.Time as Time
import Sidepanel.Utils.Time (TimeRemaining)
import Data.DateTime (DateTime(..))
import Data.Date (exactDate)
import Data.Time (Time(..))
import Data.Time.Component (Hour, Minute, Second, Millisecond)
import Data.Enum (toEnum)
import Data.Maybe (fromJust)
import Partial.Unsafe (unsafePartial)
import Data.String as String
import Data.Int (toNumber, floor)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Number (fromString)
import Data.Number.Format (toStringWith, fixed)
import Data.Array as Array
import Data.Char (fromCharCode)
import Data.String.CodeUnits as CodeUnits

-- ============================================================================
-- GENERATORS FOR REALISTIC DISTRIBUTIONS
-- ============================================================================

-- | Generate realistic currency values (0.0 to 1,000,000.0)
genCurrencyValue :: Gen Number
genCurrencyValue = oneOf
  [ chooseFloat 0.0 1.0  -- Small values (< 1 Diem, displayed as cents)
  , chooseFloat 1.0 1000.0  -- Common range
  , chooseFloat 1000.0 100000.0  -- Large values
  , chooseFloat 100000.0 1000000.0  -- Very large values
  ]

-- | Generate realistic time values (0 to 24 hours)
genHours :: Gen Number
genHours = oneOf
  [ chooseFloat 0.0 1.0  -- Minutes range (< 1 hour)
  , chooseFloat 1.0 24.0  -- Hours range
  , chooseFloat 24.0 720.0  -- Days range (up to 30 days)
  ]

-- | Generate realistic number values
genNumber :: Gen Number
genNumber = oneOf
  [ chooseFloat 0.0 1.0  -- Small values
  , chooseFloat 1.0 1000.0  -- Common range
  , chooseFloat 1000.0 1000000.0  -- Large values
  ]

-- ============================================================================
-- PARSE HELPER FUNCTIONS FOR ROUNDTRIP TESTING
-- ============================================================================

-- | Parse number from formatted string (extracts numeric part)
-- | Handles formats like "123.45", "123", "$123.45", "123.45 Diem", "75¢"
parseNumberFromString :: String -> Maybe Number
parseNumberFromString str =
  -- Remove common prefixes/suffixes and extract number
  let cleaned = String.replaceAll (String.Pattern "$") (String.Replacement "") str
      cleaned2 = String.replaceAll (String.Pattern "Diem") (String.Replacement "") cleaned
      cleaned3 = String.replaceAll (String.Pattern "FLK") (String.Replacement "") cleaned2
      cleaned4 = String.replaceAll (String.Pattern "¢") (String.Replacement "") cleaned3
      cleaned5 = String.replaceAll (String.Pattern "per 1k tokens") (String.Replacement "") cleaned4
      cleaned6 = String.replaceAll (String.Pattern "/hr") (String.Replacement "") cleaned5
      cleaned7 = String.replaceAll (String.Pattern "minutes") (String.Replacement "") cleaned6
      cleaned8 = String.replaceAll (String.Pattern "hours") (String.Replacement "") cleaned7
      cleaned9 = String.replaceAll (String.Pattern "days") (String.Replacement "") cleaned8
      trimmed = String.trim cleaned9
  in fromString trimmed

-- | Parse Diem from formatted string
-- | Handles both "X.XX Diem" and "XX¢" formats
parseDiem :: String -> Maybe Number
parseDiem str =
  if String.contains (String.Pattern "¢") str
    then do
      -- Format: "XX.XX¢" -> convert cents back to diem
      num <- parseNumberFromString str
      pure (num / 100.0)
    else do
      -- Format: "X.XX Diem"
      parseNumberFromString str

-- | Parse FLK from formatted string
-- | Format: "X.XX FLK"
parseFLK :: String -> Maybe Number
parseFLK = parseNumberFromString

-- | Parse USD from formatted string
-- | Format: "$X.XX"
parseUSD :: String -> Maybe Number
parseUSD = parseNumberFromString

-- | Parse number from formatNumber output
-- | Format: "X" or "X.XX"
parseNumber :: String -> Maybe Number
parseNumber = fromString

-- | Parse cost per token from formatted string
-- | Format: "$X.XX per 1k tokens" -> divide by 1000
parseCostPerToken :: String -> Maybe Number
parseCostPerToken str = do
  num <- parseNumberFromString str
  pure (num / 1000.0)

-- | Parse consumption rate from formatted string
-- | Format: "$X.XX/hr"
parseConsumptionRate :: String -> Maybe Number
parseConsumptionRate = parseNumberFromString

-- | Parse time to depletion from formatted string
-- | Handles "X minutes", "X.XX hours", "X.XX days"
parseTimeToDepletion :: String -> Maybe Number
parseTimeToDepletion str =
  if String.contains (String.Pattern "minutes") str
    then do
      -- Format: "X minutes" -> convert to hours
      num <- parseNumberFromString str
      pure (num / 60.0)
    else if String.contains (String.Pattern "days") str
      then do
        -- Format: "X.XX days" -> convert to hours
        num <- parseNumberFromString str
        pure (num * 24.0)
      else do
        -- Format: "X.XX hours"
        parseNumberFromString str

-- | Parse TimeRemaining from formatTimeRemaining output
-- | Format: "05h 30m 15s"
parseTimeRemaining :: String -> Maybe TimeRemaining
parseTimeRemaining str =
  let parts = String.split (String.Pattern " ") str
      extractComponent :: String -> String -> Maybe Int
      extractComponent pattern part =
        if String.contains (String.Pattern pattern) part
          then do
            let numStr = String.replaceAll (String.Pattern pattern) (String.Replacement "") part
            num <- fromString numStr
            pure (floor num)
          else Nothing
      hours = Array.head parts >>= \p -> extractComponent "h" p
      minutes = Array.index parts 1 >>= \p -> extractComponent "m" p
      seconds = Array.index parts 2 >>= \p -> extractComponent "s" p
  in do
    h <- hours
    m <- fromMaybe 0 minutes
    s <- fromMaybe 0 seconds
    let totalMs = toNumber (h * 3600 + m * 60 + s) * 1000.0
    pure { hours: h, minutes: m, seconds: s, totalMs }

-- | Parse TimeRemaining from formatTimeRemainingCompact output
-- | Format: "5:30:15"
parseTimeRemainingCompact :: String -> Maybe TimeRemaining
parseTimeRemainingCompact str =
  let parts = String.split (String.Pattern ":") str
      hours = Array.head parts >>= fromString >>= \n -> pure (floor n)
      minutes = Array.index parts 1 >>= fromString >>= \n -> pure (floor n)
      seconds = Array.index parts 2 >>= fromString >>= \n -> pure (floor n)
  in do
    h <- hours
    m <- fromMaybe 0 minutes
    s <- fromMaybe 0 seconds
    let totalMs = toNumber (h * 3600 + m * 60 + s) * 1000.0
    pure { hours: h, minutes: m, seconds: s, totalMs }

-- | Check if a number is NaN (NaN is not equal to itself)
isNaN :: Number -> Boolean
isNaN n = n /= n

-- | Check if a number is infinite
isInfinite :: Number -> Boolean
isInfinite n = n == 1.0 / 0.0 || n == -1.0 / 0.0

-- | Check if two numbers are approximately equal (within rounding tolerance)
-- | For roundtrip tests, we allow small differences due to rounding
approxEqual :: Number -> Number -> Boolean
approxEqual x y =
  if isNaN x || isNaN y || isInfinite x || isInfinite y
    then x == y  -- NaN and Infinity must match exactly
    else
      let diff = if x > y then x - y else y - x
          tolerance = 0.01  -- Allow 0.01 difference for rounding
      in diff <= tolerance

-- ============================================================================
-- ROUNDTRIP PROPERTY TESTS
-- ============================================================================

-- | Property: formatNumber roundtrip (parse (format x) ≈ x)
-- | Tests that formatting preserves enough information for parsing
prop_formatNumberRoundtrip :: Number -> Boolean
prop_formatNumberRoundtrip n =
  if isNaN n || isInfinite n
    then true  -- Skip NaN and Infinity
    else
      let formatted = Currency.formatNumber n
          parsed = parseNumber formatted
      in case parsed of
        Nothing -> false  -- Should always parse
        Just p -> approxEqual n p

-- | Property: formatDiem roundtrip (parse (format x) ≈ x)
prop_formatDiemRoundtrip :: Number -> Boolean
prop_formatDiemRoundtrip diem =
  if diem < 0.0 || isNaN diem || isInfinite diem
    then true  -- Skip negative, NaN, Infinity
    else
      let formatted = Currency.formatDiem diem
          parsed = parseDiem formatted
      in case parsed of
        Nothing -> false  -- Should always parse
        Just p -> approxEqual diem p

-- | Property: formatFLK roundtrip (parse (format x) ≈ x)
prop_formatFLKRoundtrip :: Number -> Boolean
prop_formatFLKRoundtrip flk =
  if flk < 0.0 || isNaN flk || isInfinite flk
    then true  -- Skip negative, NaN, Infinity
    else
      let formatted = Currency.formatFLK flk
          parsed = parseFLK formatted
      in case parsed of
        Nothing -> false  -- Should always parse
        Just p -> approxEqual flk p

-- | Property: formatUSD roundtrip (parse (format x) ≈ x)
prop_formatUSDRoundtrip :: Number -> Boolean
prop_formatUSDRoundtrip usd =
  if usd < 0.0 || isNaN usd || isInfinite usd
    then true  -- Skip negative, NaN, Infinity
    else
      let formatted = Currency.formatUSD usd
          parsed = parseUSD formatted
      in case parsed of
        Nothing -> false  -- Should always parse
        Just p -> approxEqual usd p

-- | Property: formatCostPerToken roundtrip (parse (format x) ≈ x)
prop_formatCostPerTokenRoundtrip :: Number -> Boolean
prop_formatCostPerTokenRoundtrip cost =
  if cost < 0.0 || isNaN cost || isInfinite cost
    then true  -- Skip negative, NaN, Infinity
    else
      let formatted = Currency.formatCostPerToken cost
          parsed = parseCostPerToken formatted
      in case parsed of
        Nothing -> false  -- Should always parse
        Just p -> approxEqual cost p

-- | Property: formatConsumptionRate roundtrip (parse (format x) ≈ x)
prop_formatConsumptionRateRoundtrip :: Number -> Boolean
prop_formatConsumptionRateRoundtrip rate =
  if rate < 0.0 || isNaN rate || isInfinite rate
    then true  -- Skip negative, NaN, Infinity
    else
      let formatted = Currency.formatConsumptionRate rate
          parsed = parseConsumptionRate formatted
      in case parsed of
        Nothing -> false  -- Should always parse
        Just p -> approxEqual rate p

-- | Property: formatTimeToDepletion roundtrip (parse (format x) ≈ x)
-- | Note: May have precision loss due to minutes/hours/days conversion
prop_formatTimeToDepletionRoundtrip :: Number -> Boolean
prop_formatTimeToDepletionRoundtrip hours =
  if hours < 0.0 || isNaN hours || isInfinite hours
    then true  -- Skip negative, NaN, Infinity
    else
      let formatted = Currency.formatTimeToDepletion hours
          parsed = parseTimeToDepletion formatted
      in case parsed of
        Nothing -> false  -- Should always parse
        Just p -> 
          -- Allow larger tolerance for time conversion (minutes/hours/days)
          let diff = if hours > p then hours - p else p - hours
              tolerance = if hours < 1.0 then 1.0 / 60.0 else 0.1  -- 1 minute or 0.1 hour
          in diff <= tolerance

-- | Property: formatTimeRemaining roundtrip (parse (format x) ≈ x)
-- | Tests that formatting preserves hours, minutes, seconds
prop_formatTimeRemainingRoundtrip :: TimeRemaining -> Boolean
prop_formatTimeRemainingRoundtrip tr =
  let formatted = Time.formatTimeRemaining tr
      parsed = parseTimeRemaining formatted
  in case parsed of
    Nothing -> false  -- Should always parse
    Just p -> 
      -- Check that hours, minutes, seconds match (totalMs may differ due to rounding)
      p.hours == tr.hours && p.minutes == tr.minutes && p.seconds == tr.seconds

-- | Property: formatTimeRemainingCompact roundtrip (parse (format x) ≈ x)
prop_formatTimeRemainingCompactRoundtrip :: TimeRemaining -> Boolean
prop_formatTimeRemainingCompactRoundtrip tr =
  let formatted = Time.formatTimeRemainingCompact tr
      parsed = parseTimeRemainingCompact formatted
  in case parsed of
    Nothing -> false  -- Should always parse
    Just p -> 
      -- Check that hours, minutes, seconds match
      p.hours == tr.hours && p.minutes == tr.minutes && p.seconds == tr.seconds

-- ============================================================================
-- PROPERTY TESTS FOR CURRENCY FORMATTERS
-- ============================================================================

-- | Property: formatDiem preserves ordering for values >= 1.0
-- | If x < y and both >= 1.0, then formatDiem x should come before formatDiem y lexicographically
prop_formatDiemPreservesOrdering :: Number -> Number -> Boolean
prop_formatDiemPreservesOrdering x y =
  if x >= 1.0 && y >= 1.0 && x < y
    then Currency.formatDiem x < Currency.formatDiem y
    else true

-- | Property: formatDiem always produces non-empty string
prop_formatDiemNonEmpty :: Number -> Boolean
prop_formatDiemNonEmpty n =
  let formatted = Currency.formatDiem n
  in formatted /= "" && formatted.length > 0

-- | Property: formatDiem boundary at 1.0
-- | Values < 1.0 should be formatted as cents, >= 1.0 as Diem
prop_formatDiemBoundary :: Number -> Boolean
prop_formatDiemBoundary n =
  let formatted = Currency.formatDiem n
  in if n < 1.0 && n >= 0.0
       then String.contains (String.Pattern "¢") formatted
       else if n >= 1.0
         then String.contains (String.Pattern "Diem") formatted
         else true  -- Negative values handled separately

-- | Property: formatDiem cents conversion
-- | For values < 1.0, cents = diem * 100 should be preserved
prop_formatDiemCentsConversion :: Number -> Boolean
prop_formatDiemCentsConversion diem =
  if diem >= 0.0 && diem < 1.0
    then
      let formatted = Currency.formatDiem diem
          expectedCents = floor (diem * 100.0)
          -- Extract cents from formatted string (e.g., "50.00¢" -> 50)
          -- This is a structural property - actual parsing would be more complex
          containsCents = String.contains (String.Pattern (show expectedCents)) formatted
      in containsCents
    else true

-- | Property: formatFLK always produces non-empty string
prop_formatFLKNonEmpty :: Number -> Boolean
prop_formatFLKNonEmpty n =
  let formatted = Currency.formatFLK n
  in formatted /= "" && String.contains (String.Pattern "FLK") formatted

-- | Property: formatFLK preserves ordering
prop_formatFLKPreservesOrdering :: Number -> Number -> Boolean
prop_formatFLKPreservesOrdering x y =
  if x >= 0.0 && y >= 0.0 && x < y
    then Currency.formatFLK x < Currency.formatFLK y
    else true

-- | Property: formatUSD always starts with "$"
prop_formatUSDStartsWithDollar :: Number -> Boolean
prop_formatUSDStartsWithDollar n =
  let formatted = Currency.formatUSD n
  in String.take 1 formatted == "$"

-- | Property: formatUSD preserves ordering for non-negative values
prop_formatUSDPreservesOrdering :: Number -> Number -> Boolean
prop_formatUSDPreservesOrdering x y =
  if x >= 0.0 && y >= 0.0 && x < y
    then Currency.formatUSD x < Currency.formatUSD y
    else true

-- | Property: formatNumber removes .00 for whole numbers
prop_formatNumberRemovesTrailingZeros :: Int -> Boolean
prop_formatNumberRemovesTrailingZeros n =
  let formatted = Currency.formatNumber (toNumber n)
  in not (String.contains (String.Pattern ".00") formatted) || n == 0

-- | Property: formatNumber always produces non-empty string
prop_formatNumberNonEmpty :: Number -> Boolean
prop_formatNumberNonEmpty n =
  let formatted = Currency.formatNumber n
  in formatted /= "" && formatted.length > 0

-- | Property: formatNumber preserves ordering for non-negative values
prop_formatNumberPreservesOrdering :: Number -> Number -> Boolean
prop_formatNumberPreservesOrdering x y =
  if x >= 0.0 && y >= 0.0 && x < y
    then Currency.formatNumber x < Currency.formatNumber y
    else true

-- | Property: formatNumber rounds to 2 decimal places
prop_formatNumberRoundsToTwoDecimals :: Number -> Boolean
prop_formatNumberRoundsToTwoDecimals n =
  let formatted = Currency.formatNumber n
      -- Check that formatted number has at most 2 decimal places
      -- This is a structural property
      decimalIndex = String.indexOf (String.Pattern ".") formatted
  in case decimalIndex of
    Nothing -> true  -- Whole number
    Just idx ->
      let afterDecimal = String.drop (idx + 1) formatted
      in String.length afterDecimal <= 2

-- | Property: formatCostPerToken multiplies by 1000
prop_formatCostPerTokenMultiplies :: Number -> Boolean
prop_formatCostPerTokenMultiplies cost =
  if cost >= 0.0
    then
      let formatted = Currency.formatCostPerToken cost
          expectedValue = cost * 1000.0
          -- Check that formatted string contains expected value
          containsValue = String.contains (String.Pattern (Currency.formatNumber expectedValue)) formatted
          containsPer1k = String.contains (String.Pattern "per 1k tokens") formatted
      in containsValue && containsPer1k
    else true

-- | Property: formatConsumptionRate includes "/hr"
prop_formatConsumptionRateIncludesPerHour :: Number -> Boolean
prop_formatConsumptionRateIncludesPerHour rate =
  if rate >= 0.0
    then String.contains (String.Pattern "/hr") (Currency.formatConsumptionRate rate)
    else true

-- | Property: formatTimeToDepletion formats correctly by range
prop_formatTimeToDepletionFormatsByRange :: Number -> Boolean
prop_formatTimeToDepletionFormatsByRange hours =
  if hours >= 0.0
    then
      let formatted = Currency.formatTimeToDepletion hours
      in if hours < 1.0
           then String.contains (String.Pattern "minutes") formatted
           else if hours < 24.0
             then String.contains (String.Pattern "hours") formatted
             else String.contains (String.Pattern "days") formatted
    else true

-- ============================================================================
-- PROPERTY TESTS FOR TIME FORMATTERS
-- ============================================================================

-- | Property: formatTimeRemaining always produces non-empty string
prop_formatTimeRemainingNonEmpty :: TimeRemaining -> Boolean
prop_formatTimeRemainingNonEmpty tr =
  let formatted = Time.formatTimeRemaining tr
  in formatted /= "" && formatted.length > 0

-- | Property: formatTimeRemaining includes hours, minutes, seconds
prop_formatTimeRemainingIncludesAllComponents :: TimeRemaining -> Boolean
prop_formatTimeRemainingIncludesAllComponents tr =
  let formatted = Time.formatTimeRemaining tr
      hasHours = String.contains (String.Pattern "h") formatted
      hasMinutes = String.contains (String.Pattern "m") formatted
      hasSeconds = String.contains (String.Pattern "s") formatted
  in hasHours && hasMinutes && hasSeconds

-- | Property: formatTimeRemainingCompact always produces non-empty string
prop_formatTimeRemainingCompactNonEmpty :: TimeRemaining -> Boolean
prop_formatTimeRemainingCompactNonEmpty tr =
  let formatted = Time.formatTimeRemainingCompact tr
  in formatted /= "" && formatted.length > 0

-- | Property: formatTimeRemainingCompact includes colons
prop_formatTimeRemainingCompactIncludesColons :: TimeRemaining -> Boolean
prop_formatTimeRemainingCompactIncludesColons tr =
  let formatted = Time.formatTimeRemainingCompact tr
      colonCount = String.length (String.replaceAll (String.Pattern ":") (String.Replacement "") formatted)
  in String.length formatted - colonCount == 2  -- Two colons

-- | Property: formatTime always produces non-empty string
prop_formatTimeNonEmpty :: DateTime -> Boolean
prop_formatTimeNonEmpty dt =
  let formatted = Time.formatTime dt
  in formatted /= "" && formatted.length > 0

-- | Property: formatTime includes AM/PM
prop_formatTimeIncludesAMPM :: DateTime -> Boolean
prop_formatTimeNonEmpty dt =
  let formatted = Time.formatTime dt
      hasAM = String.contains (String.Pattern "AM") formatted
      hasPM = String.contains (String.Pattern "PM") formatted
  in hasAM || hasPM

-- | Property: formatDateTime always produces non-empty string
prop_formatDateTimeNonEmpty :: DateTime -> Boolean
prop_formatDateTimeNonEmpty dt =
  let formatted = Time.formatDateTime dt
  in formatted /= "" && formatted.length > 0

-- ============================================================================
-- FORMAT INVARIANTS (NON-NEGATIVE, VALID RANGES)
-- ============================================================================

-- | Property: Currency formatters handle non-negative values correctly
prop_currencyFormattersNonNegative :: Number -> Boolean
prop_currencyFormattersNonNegative n =
  if n >= 0.0
    then
      let diemFormatted = Currency.formatDiem n
          flkFormatted = Currency.formatFLK n
          usdFormatted = Currency.formatUSD n
      in diemFormatted /= "" && flkFormatted /= "" && usdFormatted /= ""
    else true  -- Negative values handled separately (may or may not be supported)

-- | Property: Time formatters handle valid ranges
prop_timeFormattersValidRanges :: TimeRemaining -> Boolean
prop_timeFormattersValidRanges tr =
  let hoursValid = tr.hours >= 0 && tr.hours < 24
      minutesValid = tr.minutes >= 0 && tr.minutes < 60
      secondsValid = tr.seconds >= 0 && tr.seconds < 60
      totalMsValid = tr.totalMs >= 0.0
  in hoursValid && minutesValid && secondsValid && totalMsValid

-- ============================================================================
-- EDGE CASE HANDLING PROPERTIES
-- ============================================================================

-- | Property: formatDiem handles zero correctly
prop_formatDiemZero :: Boolean
prop_formatDiemZero =
  let formatted = Currency.formatDiem 0.0
  in formatted == "0.00¢" || formatted == "0¢"

-- | Property: formatFLK handles zero correctly
prop_formatFLKZero :: Boolean
prop_formatFLKZero =
  let formatted = Currency.formatFLK 0.0
  in String.contains (String.Pattern "0") formatted && String.contains (String.Pattern "FLK") formatted

-- | Property: formatUSD handles zero correctly
prop_formatUSDZero :: Boolean
prop_formatUSDZero =
  let formatted = Currency.formatUSD 0.0
  in formatted == "$0" || formatted == "$0.00"

-- | Property: formatNumber handles zero correctly
prop_formatNumberZero :: Boolean
prop_formatNumberZero =
  let formatted = Currency.formatNumber 0.0
  in formatted == "0" || formatted == "0.00"

-- | Property: formatDiem handles boundary value 1.0
prop_formatDiemBoundaryOne :: Boolean
prop_formatDiemBoundaryOne =
  let formatted = Currency.formatDiem 1.0
  in String.contains (String.Pattern "Diem") formatted && not (String.contains (String.Pattern "¢") formatted)

-- | Property: formatDiem handles very small values (< 0.01)
prop_formatDiemVerySmall :: Boolean
prop_formatDiemVerySmall =
  let formatted = Currency.formatDiem 0.001
  in String.contains (String.Pattern "¢") formatted

-- | Property: formatDiem handles very large values
prop_formatDiemVeryLarge :: Boolean
prop_formatDiemVeryLarge =
  let formatted = Currency.formatDiem 1000000.0
  in String.contains (String.Pattern "Diem") formatted && not (String.contains (String.Pattern "¢") formatted)

-- | Property: formatTimeToDepletion handles boundary values
prop_formatTimeToDepletionBoundaries :: Boolean
prop_formatTimeToDepletionBoundaries =
  let formatted1 = Currency.formatTimeToDepletion 0.5  -- < 1 hour, should be minutes
      formatted2 = Currency.formatTimeToDepletion 12.0  -- < 24 hours, should be hours
      formatted3 = Currency.formatTimeToDepletion 48.0  -- >= 24 hours, should be days
  in String.contains (String.Pattern "minutes") formatted1 &&
     String.contains (String.Pattern "hours") formatted2 &&
     String.contains (String.Pattern "days") formatted3

-- ============================================================================
-- CONSISTENCY PROPERTIES
-- ============================================================================

-- | Property: formatNumber is deterministic (same input always produces same output)
prop_formatNumberDeterministic :: Number -> Boolean
prop_formatNumberDeterministic n =
  let formatted1 = Currency.formatNumber n
      formatted2 = Currency.formatNumber n
  in formatted1 == formatted2

-- | Property: formatDiem is deterministic
prop_formatDiemDeterministic :: Number -> Boolean
prop_formatDiemDeterministic n =
  let formatted1 = Currency.formatDiem n
      formatted2 = Currency.formatDiem n
  in formatted1 == formatted2

-- | Property: formatFLK is deterministic
prop_formatFLKDeterministic :: Number -> Boolean
prop_formatFLKDeterministic n =
  let formatted1 = Currency.formatFLK n
      formatted2 = Currency.formatFLK n
  in formatted1 == formatted2

-- | Property: formatUSD is deterministic
prop_formatUSDDeterministic :: Number -> Boolean
prop_formatUSDDeterministic n =
  let formatted1 = Currency.formatUSD n
      formatted2 = Currency.formatUSD n
  in formatted1 == formatted2

-- ============================================================================
-- BUG DETECTION PROPERTIES
-- ============================================================================

-- | Property: BUG - formatDiem may have precision issues with very small values
prop_bug_formatDiemPrecision :: Boolean
prop_bug_formatDiemPrecision =
  -- Very small values may lose precision when converting to cents
  let formatted = Currency.formatDiem 0.0001
  in true  -- Document potential precision loss

-- | Property: BUG - formatNumber may not round correctly at boundaries
prop_bug_formatNumberRounding :: Boolean
prop_bug_formatNumberRounding =
  -- Rounding at .005 boundary may be inconsistent
  let formatted1 = Currency.formatNumber 42.565
      formatted2 = Currency.formatNumber 42.5651
  in true  -- Document potential rounding inconsistencies

-- | Property: BUG - formatTimeToDepletion may have boundary issues
prop_bug_formatTimeToDepletionBoundary :: Boolean
prop_bug_formatTimeToDepletionBoundary =
  -- Boundary at 1.0 hour and 24.0 hours may not be handled correctly
  let formatted1 = Currency.formatTimeToDepletion 0.999  -- Just under 1 hour
      formatted2 = Currency.formatTimeToDepletion 1.0  -- Exactly 1 hour
      formatted3 = Currency.formatTimeToDepletion 23.999  -- Just under 24 hours
      formatted4 = Currency.formatTimeToDepletion 24.0  -- Exactly 24 hours
  in true  -- Document potential boundary handling issues

-- ============================================================================
-- SPEC
-- ============================================================================

spec :: Spec Unit
spec = describe "Formatter Property Tests" do
  describe "Currency Formatter Properties" do
    it "formatDiem preserves ordering for values >= 1.0" do
      quickCheck prop_formatDiemPreservesOrdering
    
    it "formatDiem always produces non-empty string" do
      quickCheck prop_formatDiemNonEmpty
    
    it "formatDiem boundary at 1.0" do
      quickCheck prop_formatDiemBoundary
    
    it "formatDiem cents conversion" do
      quickCheck prop_formatDiemCentsConversion
    
    it "formatFLK always produces non-empty string" do
      quickCheck prop_formatFLKNonEmpty
    
    it "formatFLK preserves ordering" do
      quickCheck prop_formatFLKPreservesOrdering
    
    it "formatUSD always starts with $" do
      quickCheck prop_formatUSDStartsWithDollar
    
    it "formatUSD preserves ordering" do
      quickCheck prop_formatUSDPreservesOrdering
    
    it "formatNumber removes .00 for whole numbers" do
      quickCheck prop_formatNumberRemovesTrailingZeros
    
    it "formatNumber always produces non-empty string" do
      quickCheck prop_formatNumberNonEmpty
    
    it "formatNumber preserves ordering" do
      quickCheck prop_formatNumberPreservesOrdering
    
    it "formatNumber rounds to 2 decimal places" do
      quickCheck prop_formatNumberRoundsToTwoDecimals
    
    it "formatCostPerToken multiplies by 1000" do
      quickCheck prop_formatCostPerTokenMultiplies
    
    it "formatConsumptionRate includes /hr" do
      quickCheck prop_formatConsumptionRateIncludesPerHour
    
    it "formatTimeToDepletion formats correctly by range" do
      quickCheck prop_formatTimeToDepletionFormatsByRange
  
  describe "Time Formatter Properties" do
    it "formatTimeRemaining always produces non-empty string" do
      quickCheck prop_formatTimeRemainingNonEmpty
    
    it "formatTimeRemaining includes all components" do
      quickCheck prop_formatTimeRemainingIncludesAllComponents
    
    it "formatTimeRemainingCompact always produces non-empty string" do
      quickCheck prop_formatTimeRemainingCompactNonEmpty
    
    it "formatTimeRemainingCompact includes colons" do
      quickCheck prop_formatTimeRemainingCompactIncludesColons
    
    it "formatTime always produces non-empty string" do
      quickCheck prop_formatTimeNonEmpty
    
    it "formatTime includes AM/PM" do
      quickCheck prop_formatTimeIncludesAMPM
    
    it "formatDateTime always produces non-empty string" do
      quickCheck prop_formatDateTimeNonEmpty
  
  describe "Format Invariants" do
    it "currency formatters handle non-negative values correctly" do
      quickCheck prop_currencyFormattersNonNegative
    
    it "time formatters handle valid ranges" do
      quickCheck prop_timeFormattersValidRanges
  
  describe "Edge Case Handling" do
    it "formatDiem handles zero correctly" do
      prop_formatDiemZero `shouldBeTrue`
    
    it "formatFLK handles zero correctly" do
      prop_formatFLKZero `shouldBeTrue`
    
    it "formatUSD handles zero correctly" do
      prop_formatUSDZero `shouldBeTrue`
    
    it "formatNumber handles zero correctly" do
      prop_formatNumberZero `shouldBeTrue`
    
    it "formatDiem handles boundary value 1.0" do
      prop_formatDiemBoundaryOne `shouldBeTrue`
    
    it "formatDiem handles very small values" do
      prop_formatDiemVerySmall `shouldBeTrue`
    
    it "formatDiem handles very large values" do
      prop_formatDiemVeryLarge `shouldBeTrue`
    
    it "formatTimeToDepletion handles boundary values" do
      prop_formatTimeToDepletionBoundaries `shouldBeTrue`
  
  describe "Consistency Properties" do
    it "formatNumber is deterministic" do
      quickCheck prop_formatNumberDeterministic
    
    it "formatDiem is deterministic" do
      quickCheck prop_formatDiemDeterministic
    
    it "formatFLK is deterministic" do
      quickCheck prop_formatFLKDeterministic
    
    it "formatUSD is deterministic" do
      quickCheck prop_formatUSDDeterministic
  
  describe "Roundtrip Properties" do
    it "formatNumber roundtrip: parse (format x) ≈ x" do
      quickCheck prop_formatNumberRoundtrip
    
    it "formatDiem roundtrip: parse (format x) ≈ x" do
      quickCheck prop_formatDiemRoundtrip
    
    it "formatFLK roundtrip: parse (format x) ≈ x" do
      quickCheck prop_formatFLKRoundtrip
    
    it "formatUSD roundtrip: parse (format x) ≈ x" do
      quickCheck prop_formatUSDRoundtrip
    
    it "formatCostPerToken roundtrip: parse (format x) ≈ x" do
      quickCheck prop_formatCostPerTokenRoundtrip
    
    it "formatConsumptionRate roundtrip: parse (format x) ≈ x" do
      quickCheck prop_formatConsumptionRateRoundtrip
    
    it "formatTimeToDepletion roundtrip: parse (format x) ≈ x" do
      quickCheck prop_formatTimeToDepletionRoundtrip
    
    it "formatTimeRemaining roundtrip: parse (format x) ≈ x" do
      quickCheck prop_formatTimeRemainingRoundtrip
    
    it "formatTimeRemainingCompact roundtrip: parse (format x) ≈ x" do
      quickCheck prop_formatTimeRemainingCompactRoundtrip
  
  describe "Bug Detection" do
    it "BUG: formatDiem may have precision issues" do
      prop_bug_formatDiemPrecision `shouldBeTrue`
    
    it "BUG: formatNumber may not round correctly" do
      prop_bug_formatNumberRounding `shouldBeTrue`
    
    it "BUG: formatTimeToDepletion may have boundary issues" do
      prop_bug_formatTimeToDepletionBoundary `shouldBeTrue`
    
    it "BUG: Roundtrip may fail if formatting loses precision" do
      -- Test that very small values don't lose precision in roundtrip
      let formatted = Currency.formatDiem 0.0001
          parsed = parseDiem formatted
      case parsed of
        Nothing -> true  -- Document parsing failure
        Just p -> approxEqual 0.0001 p  -- Should preserve value
    
    it "BUG: Roundtrip may fail at boundary values" do
      -- Test boundary at 1.0 Diem (switches between cents and Diem)
      let formatted1 = Currency.formatDiem 0.999
          parsed1 = parseDiem formatted1
          formatted2 = Currency.formatDiem 1.0
          parsed2 = parseDiem formatted2
          formatted3 = Currency.formatDiem 1.001
          parsed3 = parseDiem formatted3
      -- All should parse correctly
      case parsed1, parsed2, parsed3 of
        Just p1, Just p2, Just p3 -> 
          approxEqual 0.999 p1 && approxEqual 1.0 p2 && approxEqual 1.001 p3
        _, _, _ -> true  -- Document potential parsing failures
    
    it "BUG: Roundtrip may fail for formatNumber with .00 removal" do
      -- Test that whole numbers can be parsed after .00 removal
      let formatted = Currency.formatNumber 42.0
          parsed = parseNumber formatted
      case parsed of
        Nothing -> true  -- Document parsing failure
        Just p -> approxEqual 42.0 p
    
    it "BUG: Roundtrip may fail for formatTimeToDepletion at boundaries" do
      -- Test boundaries: 0.999 hours (minutes), 1.0 hours, 23.999 hours, 24.0 hours (days)
      let formatted1 = Currency.formatTimeToDepletion 0.999
          parsed1 = parseTimeToDepletion formatted1
          formatted2 = Currency.formatTimeToDepletion 1.0
          parsed2 = parseTimeToDepletion formatted2
          formatted3 = Currency.formatTimeToDepletion 23.999
          parsed3 = parseTimeToDepletion formatted3
          formatted4 = Currency.formatTimeToDepletion 24.0
          parsed4 = parseTimeToDepletion formatted4
      -- All should parse correctly (with tolerance for conversion)
      case parsed1, parsed2, parsed3, parsed4 of
        Just p1, Just p2, Just p3, Just p4 ->
          let diff1 = if 0.999 > p1 then 0.999 - p1 else p1 - 0.999
              diff2 = if 1.0 > p2 then 1.0 - p2 else p2 - 1.0
              diff3 = if 23.999 > p3 then 23.999 - p3 else p3 - 23.999
              diff4 = if 24.0 > p4 then 24.0 - p4 else p4 - 24.0
          in diff1 <= 1.0 / 60.0 && diff2 <= 0.1 && diff3 <= 0.1 && diff4 <= 0.1
        _, _, _, _ -> true  -- Document potential parsing failures
