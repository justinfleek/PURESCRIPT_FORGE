-- | Validation Utilities Tests
-- | Unit and property tests for validation functions
module Test.Bridge.Utils.ValidationSpec where

import Prelude
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual, shouldBeTrue, shouldBeFalse)
import Test.QuickCheck (quickCheck, (<?>))
import Test.QuickCheck.Arbitrary (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, chooseInt, chooseFloat, arrayOf, elements, suchThat)
import Effect (Effect)
import Forge.Bridge.Utils.Validation
  ( validateNonNegative
  , validatePositive
  , validateRange
  , validateNonEmpty
  , validateLength
  , validateSessionId
  , validateJsonRpcVersion
  , validateMethodName
  , validateTimestamp
  )

-- | Arbitrary instance for non-negative numbers
newtype NonNegative = NonNegative Number
instance Arbitrary NonNegative where
  arbitrary = NonNegative <$> chooseFloat 0.0 1000.0

-- | Arbitrary instance for positive numbers
newtype Positive = Positive Number
instance Arbitrary Positive where
  arbitrary = Positive <$> chooseFloat 0.0001 1000.0

-- | Arbitrary instance for valid session IDs
newtype ValidSessionId = ValidSessionId String
instance Arbitrary ValidSessionId where
  arbitrary = do
    len <- chooseInt 1 200
    chars <- arrayOf len (elements ['a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '-', '_', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z'])
    pure $ ValidSessionId (foldChars chars)
    where
      foldChars :: Array Char -> String
      foldChars = foldl (\acc c -> acc <> singleton c) ""
      singleton :: Char -> String
      singleton c = fromCharCode (toCharCode c)
      fromCharCode :: Int -> String
      fromCharCode = fromCharCodeImpl
      toCharCode :: Char -> Int
      toCharCode = toCharCodeImpl

foreign import fromCharCodeImpl :: Int -> String
foreign import toCharCodeImpl :: Char -> Int

-- | Test non-negative validation
testNonNegative :: forall m. Monad m => m Unit
testNonNegative = do
  describe "Non-Negative Validation" do
    it "accepts zero" do
      validateNonNegative 0.0 `shouldBeTrue`
    
    it "accepts positive numbers" do
      validateNonNegative 42.0 `shouldBeTrue`
      validateNonNegative 100.5 `shouldBeTrue`
    
    it "rejects negative numbers" do
      validateNonNegative (-1.0) `shouldBeFalse`
      validateNonNegative (-100.0) `shouldBeFalse`

-- | Property: Non-negative validation holds for all non-negative numbers
prop_nonNegativeAlwaysTrue :: NonNegative -> Boolean
prop_nonNegativeAlwaysTrue (NonNegative n) = validateNonNegative n

-- | Test positive validation
testPositive :: forall m. Monad m => m Unit
testPositive = do
  describe "Positive Validation" do
    it "accepts positive numbers" do
      validatePositive 1.0 `shouldBeTrue`
      validatePositive 42.0 `shouldBeTrue`
    
    it "rejects zero" do
      validatePositive 0.0 `shouldBeFalse`
    
    it "rejects negative numbers" do
      validatePositive (-1.0) `shouldBeFalse`

-- | Property: Positive validation holds for all positive numbers
prop_positiveAlwaysTrue :: Positive -> Boolean
prop_positiveAlwaysTrue (Positive n) = validatePositive n

-- | Test range validation
testRange :: forall m. Monad m => m Unit
testRange = do
  describe "Range Validation" do
    it "accepts numbers within range" do
      validateRange 0.0 100.0 50.0 `shouldBeTrue`
      validateRange 0.0 100.0 0.0 `shouldBeTrue`
      validateRange 0.0 100.0 100.0 `shouldBeTrue`
    
    it "accepts numbers at exact boundaries" do
      validateRange 0.0 100.0 0.0 `shouldBeTrue`
      validateRange 0.0 100.0 100.0 `shouldBeTrue`
      validateRange (-10.0) 10.0 (-10.0) `shouldBeTrue`
      validateRange (-10.0) 10.0 10.0 `shouldBeTrue`
    
    it "rejects numbers below range" do
      validateRange 0.0 100.0 (-1.0) `shouldBeFalse`
      validateRange 0.0 100.0 (-100.0) `shouldBeFalse`
      validateRange 10.0 20.0 9.999999 `shouldBeFalse`
    
    it "rejects numbers above range" do
      validateRange 0.0 100.0 101.0 `shouldBeFalse`
      validateRange 0.0 100.0 200.0 `shouldBeFalse`
      validateRange 10.0 20.0 20.000001 `shouldBeFalse`
    
    it "handles negative ranges" do
      validateRange (-100.0) (-10.0) (-50.0) `shouldBeTrue`
      validateRange (-100.0) (-10.0) (-100.0) `shouldBeTrue`
      validateRange (-100.0) (-10.0) (-10.0) `shouldBeTrue`
      validateRange (-100.0) (-10.0) (-101.0) `shouldBeFalse`
      validateRange (-100.0) (-10.0) (-9.0) `shouldBeFalse`
    
    it "handles zero-width ranges" do
      validateRange 5.0 5.0 5.0 `shouldBeTrue`
      validateRange 5.0 5.0 4.999999 `shouldBeFalse`
      validateRange 5.0 5.0 5.000001 `shouldBeFalse`
    
    it "handles very large ranges" do
      validateRange 0.0 1.0e10 5.0e9 `shouldBeTrue`
      validateRange 0.0 1.0e10 (-1.0) `shouldBeFalse`
      validateRange 0.0 1.0e10 (1.0e10 + 1.0) `shouldBeFalse`
    
    it "handles very small ranges" do
      validateRange 0.0 0.000001 0.0000005 `shouldBeTrue`
      validateRange 0.0 0.000001 (-0.000001) `shouldBeFalse`
      validateRange 0.0 0.000001 0.000002 `shouldBeFalse`
    
    it "handles floating point precision edge cases" do
      validateRange 0.0 1.0 0.9999999999999999 `shouldBeTrue`
      validateRange 0.0 1.0 1.0000000000000001 `shouldBeFalse`

-- | Property: Range validation is symmetric and matches mathematical definition
prop_rangeSymmetric :: Number -> Number -> Number -> Boolean
prop_rangeSymmetric min max n = 
  if min <= max then
    let expected = n >= min && n <= max
        actual = validateRange min max n
    in actual == expected
  else
    true -- Invalid range, property doesn't apply

-- | Property: Range validation is reflexive at boundaries
prop_rangeReflexive :: Number -> Boolean
prop_rangeReflexive n = 
  validateRange n n n

-- | Property: Range validation is transitive
prop_rangeTransitive :: Number -> Number -> Number -> Number -> Boolean
prop_rangeTransitive min mid max n =
  if min <= mid && mid <= max then
    let inMinMid = validateRange min mid n
        inMidMax = validateRange mid max n
        inMinMax = validateRange min max n
    in if inMinMid && inMidMax then inMinMax else true -- If in both sub-ranges, must be in full range
  else
    true

-- | Test non-empty validation
testNonEmpty :: forall m. Monad m => m Unit
testNonEmpty = do
  describe "Non-Empty Validation" do
    it "accepts non-empty strings" do
      validateNonEmpty "test" `shouldBeTrue`
      validateNonEmpty "a" `shouldBeTrue`
    
    it "rejects empty string" do
      validateNonEmpty "" `shouldBeFalse`

-- | Property: Non-empty validation holds for all non-empty strings
prop_nonEmptyAlwaysTrue :: String -> Boolean
prop_nonEmptyAlwaysTrue s = 
  if s /= "" then
    validateNonEmpty s
  else
    not (validateNonEmpty s)

-- | Test length validation
testLength :: forall m. Monad m => m Unit
testLength = do
  describe "Length Validation" do
    it "accepts strings within length range" do
      validateLength 1 10 "test" `shouldBeTrue`
      validateLength 1 10 "a" `shouldBeTrue`
      validateLength 1 10 "1234567890" `shouldBeTrue`
    
    it "rejects strings too short" do
      validateLength 5 10 "test" `shouldBeFalse`
    
    it "rejects strings too long" do
      validateLength 1 3 "test" `shouldBeFalse`

-- | Test session ID validation
testSessionId :: forall m. Monad m => m Unit
testSessionId = do
  describe "Session ID Validation" do
    it "accepts valid session IDs" do
      validateSessionId "session-123" `shouldBeTrue`
      validateSessionId "sess_abc" `shouldBeTrue`
      validateSessionId "a" `shouldBeTrue`
      validateSessionId "session_123_abc-def" `shouldBeTrue`
      validateSessionId "SESS123" `shouldBeTrue`
    
    it "accepts boundary length session IDs" do
      let minId = "a"
      let maxId = foldl (<>) "" (replicate 200 "a")
      validateSessionId minId `shouldBeTrue`
      validateSessionId maxId `shouldBeTrue`
    
    it "rejects empty session ID" do
      validateSessionId "" `shouldBeFalse`
    
    it "rejects session ID with spaces" do
      validateSessionId "session 123" `shouldBeFalse`
      validateSessionId " session" `shouldBeFalse`
      validateSessionId "session " `shouldBeFalse`
      validateSessionId "session\t123" `shouldBeFalse`
      validateSessionId "session\n123" `shouldBeFalse`
    
    it "rejects session ID too long" do
      let longId = foldl (<>) "" (replicate 201 "a")
      validateSessionId longId `shouldBeFalse`
      let veryLongId = foldl (<>) "" (replicate 1000 "a")
      validateSessionId veryLongId `shouldBeFalse`
    
    it "rejects session ID with special characters" do
      validateSessionId "session@123" `shouldBeFalse`
      validateSessionId "session#123" `shouldBeFalse`
      validateSessionId "session$123" `shouldBeFalse`
      validateSessionId "session%123" `shouldBeFalse`
      validateSessionId "session&123" `shouldBeFalse`
      validateSessionId "session*123" `shouldBeFalse`
      validateSessionId "session(123)" `shouldBeFalse`
      validateSessionId "session[123]" `shouldBeFalse`
      validateSessionId "session{123}" `shouldBeFalse`
    
    it "accepts session IDs with various valid characters" do
      validateSessionId "abc123" `shouldBeTrue`
      validateSessionId "ABC123" `shouldBeTrue`
      validateSessionId "abc-123" `shouldBeTrue`
      validateSessionId "abc_123" `shouldBeTrue`
      validateSessionId "123abc" `shouldBeTrue`
      validateSessionId "a-b_c-1_2-3" `shouldBeTrue`

-- | Property: Valid session IDs always pass validation
prop_validSessionIdAlwaysTrue :: ValidSessionId -> Boolean
prop_validSessionIdAlwaysTrue (ValidSessionId id) = validateSessionId id

-- | Test JSON-RPC version validation
testJsonRpcVersion :: forall m. Monad m => m Unit
testJsonRpcVersion = do
  describe "JSON-RPC Version Validation" do
    it "accepts version 2.0" do
      validateJsonRpcVersion "2.0" `shouldBeTrue`
    
    it "rejects other versions" do
      validateJsonRpcVersion "1.0" `shouldBeFalse`
      validateJsonRpcVersion "3.0" `shouldBeFalse`
      validateJsonRpcVersion "" `shouldBeFalse`

-- | Test method name validation
testMethodName :: forall m. Monad m => m Unit
testMethodName = do
  describe "Method Name Validation" do
    it "accepts valid method names" do
      validateMethodName "getBalance" `shouldBeTrue`
      validateMethodName "updateSession" `shouldBeTrue`
    
    it "rejects empty method name" do
      validateMethodName "" `shouldBeFalse`
    
    it "rejects method name with spaces" do
      validateMethodName "get balance" `shouldBeFalse`
    
    it "rejects method name too long" do
      let longMethod = "a" <> (foldl (<>) "" (replicate 101 "a"))
      validateMethodName longMethod `shouldBeFalse`

-- | Test timestamp validation
testTimestamp :: forall m. Monad m => m Unit
testTimestamp = do
  describe "Timestamp Validation" do
    it "accepts ISO timestamps with Z" do
      validateTimestamp "2024-01-01T00:00:00Z" `shouldBeTrue`
      validateTimestamp "2024-12-31T23:59:59Z" `shouldBeTrue`
      validateTimestamp "1970-01-01T00:00:00Z" `shouldBeTrue`
      validateTimestamp "2099-12-31T23:59:59Z" `shouldBeTrue`
    
    it "accepts ISO timestamps with timezone offset" do
      validateTimestamp "2024-01-01T00:00:00+00:00" `shouldBeTrue`
      validateTimestamp "2024-01-01T00:00:00-05:00" `shouldBeTrue`
      validateTimestamp "2024-01-01T00:00:00+14:00" `shouldBeTrue`
      validateTimestamp "2024-01-01T00:00:00-12:00" `shouldBeTrue`
      validateTimestamp "2024-01-01T12:34:56+05:30" `shouldBeTrue`
    
    it "accepts timestamps with milliseconds" do
      validateTimestamp "2024-01-01T00:00:00.123Z" `shouldBeTrue`
      validateTimestamp "2024-01-01T00:00:00.123456Z" `shouldBeTrue`
      validateTimestamp "2024-01-01T00:00:00.123+00:00" `shouldBeTrue`
    
    it "rejects empty timestamp" do
      validateTimestamp "" `shouldBeFalse`
    
    it "rejects invalid timestamp format" do
      validateTimestamp "2024-01-01" `shouldBeFalse`
      validateTimestamp "invalid" `shouldBeFalse`
      validateTimestamp "2024/01/01T00:00:00Z" `shouldBeFalse`
      validateTimestamp "2024-01-01 00:00:00Z" `shouldBeFalse`
      validateTimestamp "2024-01-01T00:00:00" `shouldBeFalse`
      validateTimestamp "T00:00:00Z" `shouldBeFalse`
      validateTimestamp "2024-01-01T" `shouldBeFalse`
    
    it "rejects timestamps without T separator" do
      validateTimestamp "2024-01-0100:00:00Z" `shouldBeFalse`
    
    it "rejects timestamps without timezone indicator" do
      validateTimestamp "2024-01-01T00:00:00" `shouldBeFalse`
      validateTimestamp "2024-01-01T00:00:00.123" `shouldBeFalse`
    
    it "rejects malformed timezone offsets" do
      validateTimestamp "2024-01-01T00:00:00+5:00" `shouldBeFalse` -- Missing leading zero
      validateTimestamp "2024-01-01T00:00:00+05:0" `shouldBeFalse` -- Missing trailing zero
      validateTimestamp "2024-01-01T00:00:00+0500" `shouldBeFalse` -- Missing colon
      validateTimestamp "2024-01-01T00:00:00+25:00" `shouldBeFalse` -- Invalid hour
      validateTimestamp "2024-01-01T00:00:00+05:60" `shouldBeFalse` -- Invalid minute

-- | Property: Non-negative and positive are mutually exclusive
prop_nonNegativePositiveExclusive :: Number -> Boolean
prop_nonNegativePositiveExclusive n =
  if n > 0.0 then
    validateNonNegative n && validatePositive n
  else if n == 0.0 then
    validateNonNegative n && not (validatePositive n)
  else
    not (validateNonNegative n) && not (validatePositive n)

-- | Property: Length validation is consistent with string length
prop_lengthValidationConsistent :: Int -> Int -> String -> Boolean
prop_lengthValidationConsistent min max s =
  if min <= max && min >= 0 then
    let len = length s
        expected = len >= min && len <= max
        actual = validateLength min max s
    in actual == expected
  else
    true -- Invalid range, property doesn't apply

-- | Property: Session ID validation implies non-empty and length validation
prop_sessionIdImpliesNonEmptyAndLength :: String -> Boolean
prop_sessionIdImpliesNonEmptyAndLength id =
  if validateSessionId id then
    validateNonEmpty id && validateLength 1 200 id
  else
    true -- If invalid, property doesn't constrain

-- | Property: Method name validation implies non-empty and length validation
prop_methodNameImpliesNonEmptyAndLength :: String -> Boolean
prop_methodNameImpliesNonEmptyAndLength method =
  if validateMethodName method then
    validateNonEmpty method && validateLength 1 100 method
  else
    true -- If invalid, property doesn't constrain

-- | Property tests
testProperties :: forall m. Monad m => m Unit
testProperties = do
  describe "Property Tests" do
    it "non-negative validation holds for all non-negative numbers" do
      quickCheck prop_nonNegativeAlwaysTrue
    
    it "positive validation holds for all positive numbers" do
      quickCheck prop_positiveAlwaysTrue
    
    it "range validation is symmetric and matches mathematical definition" do
      quickCheck prop_rangeSymmetric
    
    it "range validation is reflexive at boundaries" do
      quickCheck prop_rangeReflexive
    
    it "range validation is transitive" do
      quickCheck prop_rangeTransitive
    
    it "non-empty validation holds for all non-empty strings" do
      quickCheck prop_nonEmptyAlwaysTrue
    
    it "non-negative and positive are mutually exclusive" do
      quickCheck prop_nonNegativePositiveExclusive
    
    it "length validation is consistent with string length" do
      quickCheck prop_lengthValidationConsistent
    
    it "valid session IDs always pass validation" do
      quickCheck prop_validSessionIdAlwaysTrue
    
    it "session ID validation implies non-empty and length validation" do
      quickCheck prop_sessionIdImpliesNonEmptyAndLength
    
    it "method name validation implies non-empty and length validation" do
      quickCheck prop_methodNameImpliesNonEmptyAndLength

foreign import replicate :: Int -> String -> String
foreign import foldl :: forall a b. (b -> a -> b) -> b -> Array a -> b
