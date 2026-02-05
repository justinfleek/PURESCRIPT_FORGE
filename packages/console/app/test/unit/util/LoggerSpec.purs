-- | Deep comprehensive tests for Logger module
-- | Tests all edge cases, JSON formatting bugs, and potential issues
module Test.Unit.Util.LoggerSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldContain)
import Data.String as String
import Data.String.Pattern (Pattern(..))
import Data.String.Replacement (Replacement(..))

import Console.App.Routes.Omega.Util.Logger
  ( LogLevel(..)
  , MetricValue(..)
  , MetricEntry
  , LogEntry
  , formatMetric
  , formatLog
  , shouldLog
  )
import Data.Map as Map
import Data.Tuple (Tuple(..))

-- | Deep comprehensive tests for Logger
spec :: Spec Unit
spec = describe "Logger Deep Tests" do
  describe "formatMetric - Empty Map" do
    it "handles empty metric entry" do
      let entry = Map.empty
      let formatted = formatMetric entry
      formatted `shouldEqual` "_metric:{}"

  describe "formatMetric - Single Entry" do
    it "formats single string metric" do
      let entry = Map.singleton "key" (MetricString "value")
      let formatted = formatMetric entry
      formatted `shouldContain` "_metric:"
      formatted `shouldContain` "\"key\""
      formatted `shouldContain` "\"value\""

    it "formats single int metric" do
      let entry = Map.singleton "count" (MetricInt 42)
      let formatted = formatMetric entry
      formatted `shouldContain` "\"count\""
      formatted `shouldContain` "42"

    it "formats single number metric" do
      let entry = Map.singleton "ratio" (MetricNumber 3.14159)
      let formatted = formatMetric entry
      formatted `shouldContain` "\"ratio\""
      formatted `shouldContain` "3.14159"

    it "formats single bool metric (true)" do
      let entry = Map.singleton "enabled" (MetricBool true)
      let formatted = formatMetric entry
      formatted `shouldContain` "\"enabled\""
      formatted `shouldContain` "true"

    it "formats single bool metric (false)" do
      let entry = Map.singleton "enabled" (MetricBool false)
      let formatted = formatMetric entry
      formatted `shouldContain` "\"enabled\""
      formatted `shouldContain` "false"

  describe "formatMetric - Multiple Entries" do
    it "formats multiple entries with comma separation" do
      let entry = Map.fromFoldable
            [ Tuple "key1" (MetricString "value1")
            , Tuple "key2" (MetricInt 42)
            , Tuple "key3" (MetricBool true)
            ]
      let formatted = formatMetric entry
      formatted `shouldContain` "\"key1\""
      formatted `shouldContain` "\"key2\""
      formatted `shouldContain` "\"key3\""
      -- Should contain commas between entries
      let commaCount = countOccurrences "," formatted
      commaCount `shouldEqual` 2

  describe "formatMetric - Edge Cases" do
    it "handles empty string value" do
      let entry = Map.singleton "key" (MetricString "")
      let formatted = formatMetric entry
      formatted `shouldContain` "\"key\""
      formatted `shouldContain` "\"\""

    it "handles string with quotes (potential JSON bug)" do
      -- BUG: formatPair doesn't escape quotes in strings!
      -- This will produce invalid JSON: "key":"value"with"quotes"
      let entry = Map.singleton "key" (MetricString "value\"with\"quotes")
      let formatted = formatMetric entry
      -- Current implementation will produce invalid JSON
      formatted `shouldContain` "\"key\""
      formatted `shouldContain` "value"
      -- This test documents the bug: quotes in strings are not escaped

    it "handles string with newlines (potential JSON bug)" do
      let entry = Map.singleton "key" (MetricString "line1\nline2")
      let formatted = formatMetric entry
      formatted `shouldContain` "\"key\""
      -- Newlines are not escaped, will produce invalid JSON

    it "handles string with backslashes (potential JSON bug)" do
      let entry = Map.singleton "key" (MetricString "path\\to\\file")
      let formatted = formatMetric entry
      formatted `shouldContain` "\"key\""
      -- Backslashes are not escaped, will produce invalid JSON

    it "handles key with special characters" do
      -- BUG: Keys with quotes will break JSON!
      let entry = Map.singleton "key\"with\"quotes" (MetricString "value")
      let formatted = formatMetric entry
      -- This will produce invalid JSON: "key"with"quotes":"value"
      formatted `shouldContain` "key"
      -- This test documents the bug: quotes in keys are not escaped

    it "handles very long string value" do
      let longValue = fold (replicate 10000 "a")
      let entry = Map.singleton "key" (MetricString longValue)
      let formatted = formatMetric entry
      formatted `shouldContain` "\"key\""
      formatted `shouldContain` longValue

    it "handles unicode characters in string" do
      let entry = Map.singleton "key" (MetricString "测试-🚀-こんにちは")
      let formatted = formatMetric entry
      formatted `shouldContain` "\"key\""
      formatted `shouldContain` "测试"

    it "handles negative int" do
      let entry = Map.singleton "count" (MetricInt (-42))
      let formatted = formatMetric entry
      formatted `shouldContain` "\"count\""
      formatted `shouldContain` "-42"

    it "handles zero int" do
      let entry = Map.singleton "count" (MetricInt 0)
      let formatted = formatMetric entry
      formatted `shouldContain` "\"count\""
      formatted `shouldContain` "0"

    it "handles very large int" do
      let entry = Map.singleton "count" (MetricInt 2147483647) -- Max Int32
      let formatted = formatMetric entry
      formatted `shouldContain` "\"count\""
      formatted `shouldContain` "2147483647"

    it "handles negative number" do
      let entry = Map.singleton "ratio" (MetricNumber (-3.14159))
      let formatted = formatMetric entry
      formatted `shouldContain` "\"ratio\""
      formatted `shouldContain` "-3.14159"

    it "handles zero number" do
      let entry = Map.singleton "ratio" (MetricNumber 0.0)
      let formatted = formatMetric entry
      formatted `shouldContain` "\"ratio\""
      formatted `shouldContain` "0.0"

    it "handles very small number" do
      let entry = Map.singleton "ratio" (MetricNumber 0.0000001)
      let formatted = formatMetric entry
      formatted `shouldContain` "\"ratio\""
      formatted `shouldContain` "0.0000001"

    it "handles very large number" do
      let entry = Map.singleton "ratio" (MetricNumber 1.0e10)
      let formatted = formatMetric entry
      formatted `shouldContain` "\"ratio\""
      formatted `shouldContain` "1.0e10"

  describe "formatLog" do
    it "formats Debug log" do
      let entry = { level: Debug, message: "test message", timestamp: "2024-01-01T12:00:00Z" }
      let formatted = formatLog entry
      formatted `shouldContain` "[2024-01-01T12:00:00Z]"
      formatted `shouldContain` "[debug]"
      formatted `shouldContain` "test message"

    it "formats Info log" do
      let entry = { level: Info, message: "info message", timestamp: "2024-01-01T12:00:00Z" }
      let formatted = formatLog entry
      formatted `shouldContain` "[info]"
      formatted `shouldContain` "info message"

    it "formats Warn log" do
      let entry = { level: Warn, message: "warning", timestamp: "2024-01-01T12:00:00Z" }
      let formatted = formatLog entry
      formatted `shouldContain` "[warn]"
      formatted `shouldContain` "warning"

    it "formats Error log" do
      let entry = { level: Error, message: "error occurred", timestamp: "2024-01-01T12:00:00Z" }
      let formatted = formatLog entry
      formatted `shouldContain` "[error]"
      formatted `shouldContain` "error occurred"

    it "handles empty message" do
      let entry = { level: Info, message: "", timestamp: "2024-01-01T12:00:00Z" }
      let formatted = formatLog entry
      formatted `shouldContain` "[info]"
      formatted `shouldContain` ""

    it "handles message with newlines" do
      let entry = { level: Info, message: "line1\nline2", timestamp: "2024-01-01T12:00:00Z" }
      let formatted = formatLog entry
      formatted `shouldContain` "line1"
      formatted `shouldContain` "line2"

    it "handles empty timestamp" do
      let entry = { level: Info, message: "test", timestamp: "" }
      let formatted = formatLog entry
      formatted `shouldContain` "[]"
      formatted `shouldContain` "test"

    it "handles very long message" do
      let longMessage = fold (replicate 10000 "a")
      let entry = { level: Info, message: longMessage, timestamp: "2024-01-01T12:00:00Z" }
      let formatted = formatLog entry
      formatted `shouldContain` longMessage

  describe "shouldLog" do
    it "returns true for Debug in non-production" do
      shouldLog { isProduction: false } Debug `shouldEqual` true

    it "returns true for Info in non-production" do
      shouldLog { isProduction: false } Info `shouldEqual` true

    it "returns true for Warn in non-production" do
      shouldLog { isProduction: false } Warn `shouldEqual` true

    it "returns true for Error in non-production" do
      shouldLog { isProduction: false } Error `shouldEqual` true

    it "returns false for Debug in production" do
      shouldLog { isProduction: true } Debug `shouldEqual` false

    it "returns true for Info in production" do
      shouldLog { isProduction: true } Info `shouldEqual` true

    it "returns true for Warn in production" do
      shouldLog { isProduction: true } Warn `shouldEqual` true

    it "returns true for Error in production" do
      shouldLog { isProduction: true } Error `shouldEqual` true

  describe "LogLevel Ordering" do
    it "Debug < Info" do
      (Debug < Info) `shouldEqual` true

    it "Info < Warn" do
      (Info < Warn) `shouldEqual` true

    it "Warn < Error" do
      (Warn < Error) `shouldEqual` true

    it "Debug < Error" do
      (Debug < Error) `shouldEqual` true

  describe "MetricValue Show Instance" do
    it "shows MetricString with quotes" do
      show (MetricString "test") `shouldEqual` "\"test\""

    it "shows MetricInt without quotes" do
      show (MetricInt 42) `shouldEqual` "42"

    it "shows MetricNumber without quotes" do
      show (MetricNumber 3.14) `shouldEqual` "3.14"

    it "shows MetricBool true" do
      show (MetricBool true) `shouldEqual` "true"

    it "shows MetricBool false" do
      show (MetricBool false) `shouldEqual` "false"

  describe "LogLevel Show Instance" do
    it "shows Debug as 'debug'" do
      show Debug `shouldEqual` "debug"

    it "shows Info as 'info'" do
      show Info `shouldEqual` "info"

    it "shows Warn as 'warn'" do
      show Warn `shouldEqual` "warn"

    it "shows Error as 'error'" do
      show Error `shouldEqual` "error"

  describe "JSON Formatting Bugs" do
    it "detects bug: quotes in string values not escaped" do
      -- This will produce invalid JSON: "key":"value"with"quotes"
      let entry = Map.singleton "key" (MetricString "value\"test\"")
      let formatted = formatMetric entry
      -- The formatted string will contain unescaped quotes, breaking JSON parsing
      -- This test documents the bug
      formatted `shouldContain` "\"value\"test\""
      -- Note: This is invalid JSON and will fail parsing

    it "detects bug: quotes in keys not escaped" do
      -- This will produce invalid JSON: "key"with"quotes":"value"
      let entry = Map.singleton "key\"test\"" (MetricString "value")
      let formatted = formatMetric entry
      -- The formatted string will contain unescaped quotes in key, breaking JSON parsing
      formatted `shouldContain` "key\"test\""
      -- Note: This is invalid JSON and will fail parsing

    it "detects bug: newlines in strings not escaped" do
      let entry = Map.singleton "key" (MetricString "line1\nline2")
      let formatted = formatMetric entry
      -- Newlines are not escaped, will produce invalid JSON
      formatted `shouldContain` "\n"
      -- Note: This is invalid JSON and will fail parsing

    it "detects bug: backslashes in strings not escaped" do
      let entry = Map.singleton "key" (MetricString "path\\to\\file")
      let formatted = formatMetric entry
      -- Backslashes are not escaped, may cause issues
      formatted `shouldContain` "\\"
      -- Note: This may cause JSON parsing issues

  describe "joinWithComma Edge Cases" do
    it "handles empty array" do
      -- joinWithComma [] should return ""
      -- This is tested via empty Map in formatMetric
      let entry = Map.empty
      let formatted = formatMetric entry
      formatted `shouldEqual` "_metric:{}"

    it "handles single element array" do
      let entry = Map.singleton "key" (MetricString "value")
      let formatted = formatMetric entry
      -- Should not have trailing comma (single element should not have comma before closing brace)
      String.contains (Pattern ",}") formatted `shouldEqual` false
      formatted `shouldContain` "\"key\""

    it "handles two element array" do
      let entry = Map.fromFoldable
            [ Tuple "key1" (MetricString "value1")
            , Tuple "key2" (MetricInt 42)
            ]
      let formatted = formatMetric entry
      -- Should have exactly one comma
      let commaCount = countOccurrences "," formatted
      commaCount `shouldEqual` 1

  where
    countOccurrences :: String -> String -> Int
    countOccurrences substr str =
      countOccurrences' (Pattern substr) str 0
      where
        countOccurrences' :: Pattern -> String -> Int -> Int
        countOccurrences' pattern s acc =
          case String.indexOf pattern s of
            Nothing -> acc
            Just idx ->
              let
                substrLen = String.length substr
                rest = String.drop (idx + substrLen) s
              in
                countOccurrences' pattern rest (acc + 1)
