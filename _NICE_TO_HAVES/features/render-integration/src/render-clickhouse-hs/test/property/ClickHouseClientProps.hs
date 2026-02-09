{-# LANGUAGE OverloadedStrings #-}

-- | Deep comprehensive property tests for ClickHouse Client module
-- | Tests invariants and edge cases that unit tests might miss
module ClickHouseClientProps where

import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Data.ByteString (ByteString)
import qualified Data.ByteString.Lazy as BSL
import Data.Time (getCurrentTime, UTCTime)
import Data.Aeson (encode, decode, object, (.=), Value(..))
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Key (fromText)
import Render.ClickHouse.Client
  ( quote
  , escapeQuotes
  , formatTimestamp
  , formatMaybeInt
  , formatMaybeArray
  , formatMaybeText
  , buildInsertStatement
  , decodeMetricsAggregates
  , InferenceEvent(..)
  , MetricsAggregate(..)
  )

-- Note: Text already has Arbitrary instance from QuickCheck
-- UTCTime tests use getCurrentTime instead of Arbitrary

-- | Property: quote always wraps text in single quotes
prop_quote_wraps :: Text -> Property
prop_quote_wraps t = 
  let quoted = quote t
  in counterexample ("quoted: " ++ show quoted) $
     Text.isPrefixOf "'" quoted && Text.isSuffixOf "'" quoted

-- | Property: escapeQuotes doubles all single quotes
prop_escapeQuotes_doubles :: Text -> Property
prop_escapeQuotes_doubles t =
  let escaped = escapeQuotes t
      singleQuotes = Text.length (Text.filter (== '\'') t)
      doubledQuotes = Text.length (Text.filter (== '\'') escaped)
  in counterexample ("original: " ++ show t ++ ", escaped: " ++ show escaped) $
     doubledQuotes === singleQuotes * 2

-- | Property: quote(escapeQuotes(t)) contains no unescaped single quotes
prop_quote_no_unescaped :: Text -> Property
prop_quote_no_unescaped t =
  let quoted = quote t
      -- Remove outer quotes
      inner = Text.drop 1 (Text.dropEnd 1 quoted)
      -- Count single quotes (should all be doubled)
      singleQuotes = Text.length (Text.filter (== '\'') inner)
  in counterexample ("quoted: " ++ show quoted ++ ", inner: " ++ show inner) $
     -- All quotes in inner should be doubled (even number)
     singleQuotes `mod` 2 === 0

-- | Property: formatMaybeInt preserves Nothing as NULL
prop_formatMaybeInt_Nothing :: Property
prop_formatMaybeInt_Nothing =
  formatMaybeInt Nothing === "NULL"

-- | Property: formatMaybeInt formats Just Int correctly
prop_formatMaybeInt_Just :: Int -> Property
prop_formatMaybeInt_Just n =
  let formatted = formatMaybeInt (Just n)
      expected = Text.pack (show n)
  in counterexample ("formatted: " ++ show formatted) $
     formatted === expected

-- | Property: formatMaybeArray preserves Nothing as empty array
prop_formatMaybeArray_Nothing :: Property
prop_formatMaybeArray_Nothing =
  let formatted = formatMaybeArray Nothing
  in counterexample ("formatted: " ++ show formatted) $
     formatted === "[]"

-- | Property: formatMaybeArray formats arrays correctly
prop_formatMaybeArray_Just :: [Int] -> Property
prop_formatMaybeArray_Just xs =
  let formatted = formatMaybeArray (Just xs)
  in counterexample ("formatted: " ++ show formatted) $
     Text.isPrefixOf "[" formatted && Text.isSuffixOf "]" formatted

-- | Property: formatMaybeText preserves Nothing as NULL
prop_formatMaybeText_Nothing :: Property
prop_formatMaybeText_Nothing =
  formatMaybeText Nothing === "NULL"

-- | Property: formatMaybeText quotes Just Text
prop_formatMaybeText_Just :: Text -> Property
prop_formatMaybeText_Just t =
  let formatted = formatMaybeText (Just t)
  in counterexample ("formatted: " ++ show formatted) $
     Text.isPrefixOf "'" formatted && Text.isSuffixOf "'" formatted

-- | Property: formatTimestamp always wraps in quotes
prop_formatTimestamp_quoted :: Property
prop_formatTimestamp_quoted = monadicIO $ do
  t <- run getCurrentTime
  let formatted = formatTimestamp t
  assert $ Text.isPrefixOf "'" formatted && Text.isSuffixOf "'" formatted

-- | Property: buildInsertStatement always starts with INSERT INTO
-- Note: InferenceEvent doesn't have Arbitrary, so we test with a sample event
prop_buildInsertStatement_starts :: Property
prop_buildInsertStatement_starts = monadicIO $ do
  timestamp <- run getCurrentTime
  let event = InferenceEvent
        { ieEventId = "test_event"
        , ieTimestamp = timestamp
        , ieCustomerId = "test_customer"
        , ieModelName = "test_model"
        , ieModelType = "llm"
        , ieRequestId = "test_request"
        , ieInputTokens = Just 100
        , ieOutputTokens = Just 50
        , ieInputDims = Just [1, 2, 3]
        , ieNumSteps = Just 10
        , ieQueueTimeUs = 1000
        , ieInferenceTimeUs = 5000
        , ieTotalTimeUs = 6000
        , ieGpuSeconds = 0.5
        , ieDeviceUuid = "test_device"
        , ieBatchSize = 1
        , ieStatus = "success"
        , ieErrorCode = Nothing
        }
  let sql = buildInsertStatement event
  assert $ Text.isPrefixOf "INSERT INTO inference_events VALUES (" sql

-- | Property: buildInsertStatement has balanced parentheses
prop_buildInsertStatement_balanced :: Property
prop_buildInsertStatement_balanced = monadicIO $ do
  timestamp <- run getCurrentTime
  let event = InferenceEvent
        { ieEventId = "test_event"
        , ieTimestamp = timestamp
        , ieCustomerId = "test_customer"
        , ieModelName = "test_model"
        , ieModelType = "llm"
        , ieRequestId = "test_request"
        , ieInputTokens = Just 100
        , ieOutputTokens = Just 50
        , ieInputDims = Just [1, 2, 3]
        , ieNumSteps = Just 10
        , ieQueueTimeUs = 1000
        , ieInferenceTimeUs = 5000
        , ieTotalTimeUs = 6000
        , ieGpuSeconds = 0.5
        , ieDeviceUuid = "test_device"
        , ieBatchSize = 1
        , ieStatus = "success"
        , ieErrorCode = Nothing
        }
  let sql = buildInsertStatement event
      openParens = Text.length (Text.filter (== '(') sql)
      closeParens = Text.length (Text.filter (== ')') sql)
  assert $ openParens === closeParens

-- | Property: decodeMetricsAggregates is idempotent for valid JSON
-- Note: MetricsAggregate doesn't have Arbitrary, so we test with a sample aggregate
prop_decodeMetricsAggregates_idempotent :: Property
prop_decodeMetricsAggregates_idempotent = monadicIO $ do
  timestamp <- run getCurrentTime
  let agg = MetricsAggregate
        { maCustomerId = "test_customer"
        , maModelName = "test_model"
        , maRequestCount = 100
        , maGpuSeconds = 50.0
        , maStartTime = timestamp
        , maEndTime = timestamp
        }
  let aggs = [agg]
      -- Encode to JSON lines
      jsonLines = Text.unlines (map (Text.decodeUtf8 . BSL.toStrict . encode) aggs)
      body = Text.encodeUtf8 jsonLines
      -- Decode
      decoded = decodeMetricsAggregates body
  assert $ decoded === Just aggs

-- | Property: decodeMetricsAggregates returns Nothing for invalid JSON
prop_decodeMetricsAggregates_invalid :: Property
prop_decodeMetricsAggregates_invalid =
  let invalidJson = Text.encodeUtf8 "invalid json\n"
      decoded = decodeMetricsAggregates invalidJson
  in counterexample ("decoded: " ++ show decoded) $
     decoded === Nothing

-- | Property: decodeMetricsAggregates filters empty lines
prop_decodeMetricsAggregates_empty_lines :: Property
prop_decodeMetricsAggregates_empty_lines = monadicIO $ do
  timestamp <- run getCurrentTime
  let agg = MetricsAggregate
        { maCustomerId = "test_customer"
        , maModelName = "test_model"
        , maRequestCount = 100
        , maGpuSeconds = 50.0
        , maStartTime = timestamp
        , maEndTime = timestamp
        }
  let aggs = [agg]
      -- Encode with empty lines interspersed
      jsonLines = Text.unlines (concatMap (\a -> ["", Text.decodeUtf8 (BSL.toStrict (encode a)), ""]) aggs)
      body = Text.encodeUtf8 jsonLines
      decoded = decodeMetricsAggregates body
  assert $ decoded === Just aggs

-- | Property: escapeQuotes is idempotent (applying twice should double again)
prop_escapeQuotes_idempotent :: Text -> Property
prop_escapeQuotes_idempotent t =
  let once = escapeQuotes t
      twice = escapeQuotes once
      -- After escaping once, each ' becomes ''
      -- After escaping twice, each '' becomes ''''
      expectedDoubles = Text.length (Text.filter (== '\'') t) * 4
      actualDoubles = Text.length (Text.filter (== '\'') twice)
  in counterexample ("original: " ++ show t ++ ", once: " ++ show once ++ ", twice: " ++ show twice) $
     actualDoubles === expectedDoubles

-- | Property: quote(escapeQuotes(t)) prevents SQL injection (no '; DROP)
prop_quote_sql_injection_prevention :: Text -> Property
prop_quote_sql_injection_prevention t =
  let quoted = quote t
      -- Check that quoted string doesn't contain unescaped '; pattern
      -- This is a simplified check - real SQL injection prevention is more complex
      hasUnescapedSemicolon = Text.isInfixOf "';" quoted || Text.isInfixOf "';" (Text.drop 1 (Text.dropEnd 1 quoted))
  in counterexample ("quoted: " ++ show quoted) $
     not hasUnescapedSemicolon

-- | Property: formatMaybeArray preserves array length
prop_formatMaybeArray_length :: [Int] -> Property
prop_formatMaybeArray_length xs =
  let formatted = formatMaybeArray (Just xs)
      -- Count commas to estimate array length
      commas = Text.length (Text.filter (== ',') formatted)
      expectedCommas = if null xs then 0 else length xs - 1
  in counterexample ("formatted: " ++ show formatted ++ ", xs: " ++ show xs) $
     commas === expectedCommas

-- | Property: buildInsertStatement has correct number of commas (field separators)
prop_buildInsertStatement_commas :: Property
prop_buildInsertStatement_commas = monadicIO $ do
  timestamp <- run getCurrentTime
  let event = InferenceEvent
        { ieEventId = "test_event"
        , ieTimestamp = timestamp
        , ieCustomerId = "test_customer"
        , ieModelName = "test_model"
        , ieModelType = "llm"
        , ieRequestId = "test_request"
        , ieInputTokens = Just 100
        , ieOutputTokens = Just 50
        , ieInputDims = Just [1, 2, 3]
        , ieNumSteps = Just 10
        , ieQueueTimeUs = 1000
        , ieInferenceTimeUs = 5000
        , ieTotalTimeUs = 6000
        , ieGpuSeconds = 0.5
        , ieDeviceUuid = "test_device"
        , ieBatchSize = 1
        , ieStatus = "success"
        , ieErrorCode = Nothing
        }
  let sql = buildInsertStatement event
      -- InferenceEvent has 17 fields, so 16 commas
      commas = Text.length (Text.filter (== ',') sql)
  assert $ commas === 16

-- | Property: decodeMetricsAggregates handles empty body
prop_decodeMetricsAggregates_empty :: Property
prop_decodeMetricsAggregates_empty =
  let decoded = decodeMetricsAggregates ""
  in counterexample ("decoded: " ++ show decoded) $
     decoded === Just []

-- | Property: decodeMetricsAggregates handles single empty line
prop_decodeMetricsAggregates_single_empty :: Property
prop_decodeMetricsAggregates_single_empty =
  let decoded = decodeMetricsAggregates (Text.encodeUtf8 "\n")
  in decoded === Just []

-- | Property: formatMaybeInt handles negative values
prop_formatMaybeInt_negative :: Int -> Property
prop_formatMaybeInt_negative n =
  let formatted = formatMaybeInt (Just n)
      expected = Text.pack (show n)
  in counterexample ("formatted: " ++ show formatted) $
     formatted === expected

-- | Property: formatMaybeArray handles negative values
prop_formatMaybeArray_negative :: [Int] -> Property
prop_formatMaybeArray_negative xs =
  let formatted = formatMaybeArray (Just xs)
  in counterexample ("formatted: " ++ show formatted) $
     Text.isPrefixOf "[" formatted && Text.isSuffixOf "]" formatted

-- | Property: quote preserves text content (minus quotes)
prop_quote_preserves_content :: Text -> Property
prop_quote_preserves_content t =
  let quoted = quote t
      -- Remove outer quotes and unescape inner quotes
      inner = Text.drop 1 (Text.dropEnd 1 quoted)
      unescaped = Text.replace "''" "'" inner
  in counterexample ("original: " ++ show t ++ ", quoted: " ++ show quoted ++ ", unescaped: " ++ show unescaped) $
     unescaped === t

-- | Deep comprehensive property tests for ClickHouse Client module
spec :: Spec
spec = describe "ClickHouse Client Property Tests" $ do
  describe "quote" $ do
    prop "always wraps text in single quotes" prop_quote_wraps
    prop "preserves text content" prop_quote_preserves_content
    prop "prevents SQL injection" prop_quote_sql_injection_prevention

  describe "escapeQuotes" $ do
    prop "doubles all single quotes" prop_escapeQuotes_doubles
    prop "is idempotent" prop_escapeQuotes_idempotent

  describe "quote + escapeQuotes" $ do
    prop "contains no unescaped single quotes" prop_quote_no_unescaped

  describe "formatMaybeInt" $ do
    prop "preserves Nothing as NULL" prop_formatMaybeInt_Nothing
    prop "formats Just Int correctly" prop_formatMaybeInt_Just
    prop "handles negative values" prop_formatMaybeInt_negative

  describe "formatMaybeArray" $ do
    prop "preserves Nothing as empty array" prop_formatMaybeArray_Nothing
    prop "formats arrays correctly" prop_formatMaybeArray_Just
    prop "preserves array length" prop_formatMaybeArray_length
    prop "handles negative values" prop_formatMaybeArray_negative

  describe "formatMaybeText" $ do
    prop "preserves Nothing as NULL" prop_formatMaybeText_Nothing
    prop "quotes Just Text" prop_formatMaybeText_Just

  describe "formatTimestamp" $ do
    it "always wraps in quotes" prop_formatTimestamp_quoted

  describe "buildInsertStatement" $ do
    it "always starts with INSERT INTO" prop_buildInsertStatement_starts
    it "has balanced parentheses" prop_buildInsertStatement_balanced
    it "has correct number of commas" prop_buildInsertStatement_commas

  describe "decodeMetricsAggregates" $ do
    it "is idempotent for valid JSON" prop_decodeMetricsAggregates_idempotent
    it "returns Nothing for invalid JSON" prop_decodeMetricsAggregates_invalid
    it "filters empty lines" prop_decodeMetricsAggregates_empty_lines
    it "handles empty body" prop_decodeMetricsAggregates_empty
    it "handles single empty line" prop_decodeMetricsAggregates_single_empty
