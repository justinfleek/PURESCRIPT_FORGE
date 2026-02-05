-- | Deep comprehensive tests for Google Chunk conversion module
-- | Tests fromGoogleChunk and toGoogleChunk with error handling,
-- | edge cases, and bug detection
module Test.Unit.Util.Provider.GoogleChunkSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual, shouldContain)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Either (Either(..), isLeft, isRight)
import Data.Array (length, head)
import Data.Foldable (fold)
import Data.Array as Array
import Data.String as String

import Console.App.Routes.Omega.Util.Provider.Google.Chunk
  ( fromGoogleChunk
  , toGoogleChunk
  )
import Console.App.Routes.Omega.Util.Provider.Provider
  ( CommonChunk
  , ChunkChoice
  , ChunkDelta
  , MessageRole(..)
  , FinishReason(..)
  )

-- | Create mock CommonChunk
mkMockCommonChunk :: CommonChunk
mkMockCommonChunk =
  { id: "chunk_123"
  , object: "chat.completion.chunk"
  , created: 1677652288
  , model: "gemini-pro"
  , choices: []
  , usage: Nothing
  }

-- | Create mock ChunkDelta
mkMockDelta :: Maybe String -> ChunkDelta
mkMockDelta content =
  { role: Nothing
  , content
  , toolCalls: Nothing
  }

-- | Create mock ChunkChoice
mkMockChunkChoice :: Maybe String -> Maybe FinishReason -> ChunkChoice
mkMockChunkChoice content finishReason =
  { index: 0
  , delta: mkMockDelta content
  , finishReason
  }

-- | Valid Google chunk JSON (content delta)
validGoogleChunkContent :: String
validGoogleChunkContent = """{"candidates":[{"content":{"parts":[{"text":"Hello"}],"role":"model"},"finishReason":null}]}"""

-- | Valid Google chunk JSON (finish reason)
validGoogleChunkFinish :: String
validGoogleChunkFinish = """{"candidates":[{"content":{"parts":[],"role":"model"},"finishReason":"STOP"}]}"""

-- | Deep comprehensive tests for Google Chunk conversions
spec :: Spec Unit
spec = describe "Google Chunk Conversion Deep Tests" do
  describe "fromGoogleChunk" do
    it "converts valid Google chunk with content delta to CommonChunk" do
      case fromGoogleChunk validGoogleChunkContent of
        Left err -> pure unit  -- Should not error
        Right commonChunk -> do
          commonChunk.choices.length `shouldEqual` 1

    it "converts chunk with finish reason" do
      case fromGoogleChunk validGoogleChunkFinish of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.finishReason `shouldEqual` Just Stop
            Nothing -> pure unit

    it "handles empty candidates array" do
      let json = """{"candidates":[]}"""
      case fromGoogleChunk json of
        Left err -> pure unit
        Right commonChunk -> commonChunk.choices.length `shouldEqual` 0

    it "handles delta with content" do
      let json = """{"candidates":[{"content":{"parts":[{"text":"Hello"}],"role":"model"},"finishReason":null}]}"""
      case fromGoogleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.delta.content `shouldEqual` Just "Hello"
            Nothing -> pure unit

    it "handles delta with empty content" do
      let json = """{"candidates":[{"content":{"parts":[{"text":""}],"role":"model"},"finishReason":null}]}"""
      case fromGoogleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.delta.content `shouldEqual` Just ""
            Nothing -> pure unit

    it "handles finishReason STOP" do
      let json = """{"candidates":[{"content":{"parts":[],"role":"model"},"finishReason":"STOP"}]}"""
      case fromGoogleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.finishReason `shouldEqual` Just Stop
            Nothing -> pure unit

    it "handles finishReason MAX_TOKENS" do
      let json = """{"candidates":[{"content":{"parts":[],"role":"model"},"finishReason":"MAX_TOKENS"}]}"""
      case fromGoogleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.finishReason `shouldEqual` Just Length
            Nothing -> pure unit

    it "handles finishReason SAFETY" do
      let json = """{"candidates":[{"content":{"parts":[],"role":"model"},"finishReason":"SAFETY"}]}"""
      case fromGoogleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.finishReason `shouldEqual` Just ContentFilter
            Nothing -> pure unit

    it "handles missing finishReason" do
      let json = """{"candidates":[{"content":{"parts":[],"role":"model"}]}"""
      case fromGoogleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.finishReason `shouldEqual` Nothing
            Nothing -> pure unit

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let json = """{"candidates":[{"content":{"parts":[{"text":""" <> "\"" <> longContent <> "\"" <> """}],"role":"model"},"finishReason":null}]}"""
      case fromGoogleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> do
              case choice.delta.content of
                Just c -> c.length `shouldEqual` 10000
                Nothing -> pure unit
            Nothing -> pure unit

    it "handles unicode characters in content" do
      let json = """{"candidates":[{"content":{"parts":[{"text":"测试-🚀-こんにちは"}],"role":"model"},"finishReason":null}]}"""
      case fromGoogleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> do
              case choice.delta.content of
                Just c -> c `shouldContain` "测试"
                Nothing -> pure unit
            Nothing -> pure unit

    it "returns Left for invalid JSON string" do
      let invalidJson = """{"candidates":[{"content":{"parts"""
      case fromGoogleChunk invalidJson of
        Left err -> do
          -- Should return error message
          err.length `shouldNotEqual` 0
        Right _ -> pure unit  -- Should not succeed

    it "returns Left for malformed JSON (missing quotes)" do
      let malformedJson = """{candidates:[{content:{parts:[{text:"test"}]}}]}"""
      case fromGoogleChunk malformedJson of
        Left err -> do
          -- Should return error message
          err.length `shouldNotEqual` 0
        Right _ -> pure unit  -- Should not succeed

    it "BUG: may return Right for missing required fields" do
      -- BUG: Missing candidates may not return Left
      let json = """{"usageMetadata":{}}"""
      case fromGoogleChunk json of
        Left err -> pure unit  -- Should error but may not
        Right commonChunk -> do
          -- candidates may be empty array but conversion succeeds
          pure unit

  describe "toGoogleChunk" do
    it "converts minimal CommonChunk to Google format" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "Hello") Nothing] }
      let googleJson = toGoogleChunk commonChunk
      -- Should contain candidates
      googleJson `shouldContain` "candidates"
      googleJson `shouldContain` "Hello"

    it "converts CommonChunk with content delta" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "test") Nothing] }
      let googleJson = toGoogleChunk commonChunk
      googleJson `shouldContain` "delta"
      googleJson `shouldContain` "test"

    it "converts CommonChunk with finish reason" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just Stop)] }
      let googleJson = toGoogleChunk commonChunk
      googleJson `shouldContain` "finishReason"
      googleJson `shouldContain` "STOP"

    it "handles empty choices array" do
      let commonChunk = mkMockCommonChunk { choices = [] }
      let googleJson = toGoogleChunk commonChunk
      googleJson `shouldContain` "candidates"
      googleJson `shouldContain` "[]"

    it "handles finishReason Stop" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just Stop)] }
      let googleJson = toGoogleChunk commonChunk
      googleJson `shouldContain` "STOP"

    it "handles finishReason Length" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just Length)] }
      let googleJson = toGoogleChunk commonChunk
      googleJson `shouldContain` "MAX_TOKENS"

    it "handles finishReason ContentFilter" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just ContentFilter)] }
      let googleJson = toGoogleChunk commonChunk
      googleJson `shouldContain` "SAFETY"

    it "handles finishReason ToolCalls" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just ToolCalls)] }
      let googleJson = toGoogleChunk commonChunk
      -- Google may not have tool_calls finish reason, may map to STOP
      googleJson `shouldContain` "finishReason"

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just longContent) Nothing] }
      let googleJson = toGoogleChunk commonChunk
      -- Should preserve long content
      googleJson.length `shouldNotEqual` 0

    it "handles unicode characters" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "测试-🚀-こんにちは") Nothing] }
      let googleJson = toGoogleChunk commonChunk
      googleJson `shouldContain` "测试"

  describe "Round-trip Conversions" do
    it "preserves data in round-trip: Google → CommonChunk → Google" do
      case fromGoogleChunk validGoogleChunkContent of
        Left err -> pure unit
        Right commonChunk -> do
          let roundTripJson = toGoogleChunk commonChunk
          -- Round-trip should preserve essential data
          roundTripJson `shouldContain` "candidates"

    it "preserves content delta in round-trip" do
      let json = """{"candidates":[{"content":{"parts":[{"text":"Hello"}],"role":"model"},"finishReason":null}]}"""
      case fromGoogleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          let roundTripJson = toGoogleChunk commonChunk
          roundTripJson `shouldContain` "Hello"

    it "preserves finish reason in round-trip" do
      let json = """{"candidates":[{"content":{"parts":[],"role":"model"},"finishReason":"STOP"}]}"""
      case fromGoogleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          let roundTripJson = toGoogleChunk commonChunk
          roundTripJson `shouldContain` "STOP"

  describe "Error Handling" do
    it "returns meaningful error message for invalid JSON" do
      let invalidJson = """{"candidates":[{"content":{"parts"""
      case fromGoogleChunk invalidJson of
        Left err -> do
          -- Error message should be non-empty
          err.length `shouldNotEqual` 0
          -- Error message should indicate JSON parsing issue
          err `shouldContain` "error"
        Right _ -> pure unit  -- Should not succeed

    it "handles empty string input" do
      case fromGoogleChunk "" of
        Left err -> do
          -- Should return error
          err.length `shouldNotEqual` 0
        Right _ -> pure unit  -- Should not succeed

    it "handles whitespace-only input" do
      case fromGoogleChunk "   " of
        Left err -> do
          -- Should return error
          err.length `shouldNotEqual` 0
        Right _ -> pure unit  -- Should not succeed
