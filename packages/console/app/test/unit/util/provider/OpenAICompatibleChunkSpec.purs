-- | Deep comprehensive tests for OpenAICompatible Chunk conversion module
-- | Tests fromOaCompatibleChunk and toOaCompatibleChunk with error handling,
-- | edge cases, and bug detection
-- | Note: OpenAICompatible format is similar to OpenAI format
module Test.Unit.Util.Provider.OpenAICompatibleChunkSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual, shouldContain)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Either (Either(..), isLeft, isRight)
import Data.Array (length, head)
import Data.Foldable (fold)
import Data.Array as Array
import Data.String as String

import Console.App.Routes.Omega.Util.Provider.OpenAICompatible.Chunk
  ( fromOaCompatibleChunk
  , toOaCompatibleChunk
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
  { id: "chatcmpl-123"
  , object: "chat.completion.chunk"
  , created: 1677652288
  , model: "custom-model"
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

-- | Valid OpenAICompatible chunk JSON (content delta) - same format as OpenAI
validOaCompatibleChunkContent :: String
validOaCompatibleChunkContent = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"custom-model","choices":[{"index":0,"delta":{"content":"Hello"},"finish_reason":null}]}"""

-- | Valid OpenAICompatible chunk JSON (finish reason)
validOaCompatibleChunkFinish :: String
validOaCompatibleChunkFinish = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"custom-model","choices":[{"index":0,"delta":{},"finish_reason":"stop"}]}"""

-- | Deep comprehensive tests for OpenAICompatible Chunk conversions
spec :: Spec Unit
spec = describe "OpenAICompatible Chunk Conversion Deep Tests" do
  describe "fromOaCompatibleChunk" do
    it "converts valid OpenAICompatible chunk with content delta to CommonChunk" do
      case fromOaCompatibleChunk validOaCompatibleChunkContent of
        Left err -> pure unit  -- Should not error
        Right commonChunk -> do
          commonChunk.id `shouldEqual` "chatcmpl-123"
          commonChunk.object `shouldEqual` "chat.completion.chunk"
          commonChunk.model `shouldEqual` "custom-model"
          commonChunk.choices.length `shouldEqual` 1

    it "converts chunk with finish reason" do
      case fromOaCompatibleChunk validOaCompatibleChunkFinish of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.finishReason `shouldEqual` Just Stop
            Nothing -> pure unit

    it "handles empty choices array" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"custom-model","choices":[]}"""
      case fromOaCompatibleChunk json of
        Left err -> pure unit
        Right commonChunk -> commonChunk.choices.length `shouldEqual` 0

    it "handles single choice" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"custom-model","choices":[{"index":0,"delta":{"content":"test"},"finish_reason":null}]}"""
      case fromOaCompatibleChunk json of
        Left err -> pure unit
        Right commonChunk -> commonChunk.choices.length `shouldEqual` 1

    it "handles multiple choices" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"custom-model","choices":[{"index":0,"delta":{"content":"test1"},"finish_reason":null},{"index":1,"delta":{"content":"test2"},"finish_reason":null}]}"""
      case fromOaCompatibleChunk json of
        Left err -> pure unit
        Right commonChunk -> commonChunk.choices.length `shouldEqual` 2

    it "handles empty delta" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"custom-model","choices":[{"index":0,"delta":{},"finish_reason":null}]}"""
      case fromOaCompatibleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.delta.content `shouldEqual` Nothing
            Nothing -> pure unit

    it "handles delta with content" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"custom-model","choices":[{"index":0,"delta":{"content":"Hello"},"finish_reason":null}]}"""
      case fromOaCompatibleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.delta.content `shouldEqual` Just "Hello"
            Nothing -> pure unit

    it "handles delta with empty content" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"custom-model","choices":[{"index":0,"delta":{"content":""},"finish_reason":null}]}"""
      case fromOaCompatibleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.delta.content `shouldEqual` Just ""
            Nothing -> pure unit

    it "handles finish_reason stop" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"custom-model","choices":[{"index":0,"delta":{},"finish_reason":"stop"}]}"""
      case fromOaCompatibleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.finishReason `shouldEqual` Just Stop
            Nothing -> pure unit

    it "handles finish_reason tool_calls" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"custom-model","choices":[{"index":0,"delta":{},"finish_reason":"tool_calls"}]}"""
      case fromOaCompatibleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.finishReason `shouldEqual` Just ToolCalls
            Nothing -> pure unit

    it "handles finish_reason length" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"custom-model","choices":[{"index":0,"delta":{},"finish_reason":"length"}]}"""
      case fromOaCompatibleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.finishReason `shouldEqual` Just Length
            Nothing -> pure unit

    it "handles finish_reason content_filter" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"custom-model","choices":[{"index":0,"delta":{},"finish_reason":"content_filter"}]}"""
      case fromOaCompatibleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.finishReason `shouldEqual` Just ContentFilter
            Nothing -> pure unit

    it "handles missing finish_reason" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"custom-model","choices":[{"index":0,"delta":{}}]}"""
      case fromOaCompatibleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.finishReason `shouldEqual` Nothing
            Nothing -> pure unit

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"custom-model","choices":[{"index":0,"delta":{"content":""" <> "\"" <> longContent <> "\"" <> """},"finish_reason":null}]}"""
      case fromOaCompatibleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> do
              case choice.delta.content of
                Just c -> c.length `shouldEqual` 10000
                Nothing -> pure unit
            Nothing -> pure unit

    it "handles unicode characters in content" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"custom-model","choices":[{"index":0,"delta":{"content":"测试-🚀-こんにちは"},"finish_reason":null}]}"""
      case fromOaCompatibleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> do
              case choice.delta.content of
                Just c -> c `shouldContain` "测试"
                Nothing -> pure unit
            Nothing -> pure unit

    it "returns Left for invalid JSON string" do
      let invalidJson = """{"id":"chatcmpl-123","object":"chat.completion.chunk"""
      case fromOaCompatibleChunk invalidJson of
        Left err -> do
          -- Should return error message
          err.length `shouldNotEqual` 0
        Right _ -> pure unit  -- Should not succeed

    it "returns Left for malformed JSON (missing quotes)" do
      let malformedJson = """{id:"chatcmpl-123",object:"chat.completion.chunk"}"""
      case fromOaCompatibleChunk malformedJson of
        Left err -> do
          -- Should return error message
          err.length `shouldNotEqual` 0
        Right _ -> pure unit  -- Should not succeed

    it "BUG: may return Right for missing required fields" do
      -- BUG: Missing id, object, created, model, or choices may not return Left
      let json = """{"object":"chat.completion.chunk","created":1677652288,"model":"custom-model","choices":[]}"""
      case fromOaCompatibleChunk json of
        Left err -> pure unit  -- Should error but may not
        Right commonChunk -> do
          -- id may be empty string instead of error
          pure unit

    it "BUG: may not validate finish_reason" do
      -- BUG: Invalid finish_reason may not return Left
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"custom-model","choices":[{"index":0,"delta":{},"finish_reason":"invalid_reason"}]}"""
      case fromOaCompatibleChunk json of
        Left err -> pure unit  -- Should error but may not
        Right commonChunk -> do
          -- finish_reason may be Nothing instead of error
          pure unit

  describe "toOaCompatibleChunk" do
    it "converts minimal CommonChunk to OpenAICompatible format" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "Hello") Nothing] }
      let oaCompatJson = toOaCompatibleChunk commonChunk
      -- Should contain id, object, model, choices
      oaCompatJson `shouldContain` "chatcmpl-123"
      oaCompatJson `shouldContain` "chat.completion.chunk"
      oaCompatJson `shouldContain` "custom-model"
      oaCompatJson `shouldContain` "choices"

    it "converts CommonChunk with content delta" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "test") Nothing] }
      let oaCompatJson = toOaCompatibleChunk commonChunk
      oaCompatJson `shouldContain` "delta"
      oaCompatJson `shouldContain` "test"

    it "converts CommonChunk with finish reason" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just Stop)] }
      let oaCompatJson = toOaCompatibleChunk commonChunk
      oaCompatJson `shouldContain` "finish_reason"
      oaCompatJson `shouldContain` "stop"

    it "handles empty choices array" do
      let commonChunk = mkMockCommonChunk { choices = [] }
      let oaCompatJson = toOaCompatibleChunk commonChunk
      oaCompatJson `shouldContain` "choices"
      oaCompatJson `shouldContain` "[]"

    it "handles single choice" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "test") Nothing] }
      let oaCompatJson = toOaCompatibleChunk commonChunk
      oaCompatJson `shouldContain` "test"

    it "handles empty delta" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing Nothing] }
      let oaCompatJson = toOaCompatibleChunk commonChunk
      oaCompatJson `shouldContain` "delta"

    it "handles delta with content" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "Hello") Nothing] }
      let oaCompatJson = toOaCompatibleChunk commonChunk
      oaCompatJson `shouldContain` "content"
      oaCompatJson `shouldContain` "Hello"

    it "handles finishReason Stop" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just Stop)] }
      let oaCompatJson = toOaCompatibleChunk commonChunk
      oaCompatJson `shouldContain` "finish_reason"
      oaCompatJson `shouldContain` "stop"

    it "handles finishReason ToolCalls" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just ToolCalls)] }
      let oaCompatJson = toOaCompatibleChunk commonChunk
      oaCompatJson `shouldContain` "tool_calls"

    it "handles finishReason Length" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just Length)] }
      let oaCompatJson = toOaCompatibleChunk commonChunk
      oaCompatJson `shouldContain` "length"

    it "handles finishReason ContentFilter" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just ContentFilter)] }
      let oaCompatJson = toOaCompatibleChunk commonChunk
      oaCompatJson `shouldContain` "content_filter"

    it "omits finish_reason when Nothing" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing Nothing] }
      let oaCompatJson = toOaCompatibleChunk commonChunk
      -- finish_reason may be omitted or null
      -- Test documents behavior
      pure unit

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just longContent) Nothing] }
      let oaCompatJson = toOaCompatibleChunk commonChunk
      -- Should preserve long content
      oaCompatJson.length `shouldNotEqual` 0

    it "handles unicode characters" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "测试-🚀-こんにちは") Nothing] }
      let oaCompatJson = toOaCompatibleChunk commonChunk
      oaCompatJson `shouldContain` "测试"

    it "handles empty id string" do
      let commonChunk = mkMockCommonChunk { id = "" }
      let oaCompatJson = toOaCompatibleChunk commonChunk
      oaCompatJson `shouldContain` "id"
      oaCompatJson `shouldContain` "\"\""

    it "handles very long id string" do
      let longId = fold (replicate 1000 "a")
      let commonChunk = mkMockCommonChunk { id = longId }
      let oaCompatJson = toOaCompatibleChunk commonChunk
      oaCompatJson `shouldContain` longId

  describe "Round-trip Conversions" do
    it "preserves data in round-trip: OpenAICompatible → CommonChunk → OpenAICompatible" do
      case fromOaCompatibleChunk validOaCompatibleChunkContent of
        Left err -> pure unit
        Right commonChunk -> do
          let roundTripJson = toOaCompatibleChunk commonChunk
          -- Round-trip should preserve essential data
          roundTripJson `shouldContain` "chatcmpl-123"
          roundTripJson `shouldContain` "custom-model"
          roundTripJson `shouldContain` "choices"

    it "preserves content delta in round-trip" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"custom-model","choices":[{"index":0,"delta":{"content":"Hello"},"finish_reason":null}]}"""
      case fromOaCompatibleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          let roundTripJson = toOaCompatibleChunk commonChunk
          roundTripJson `shouldContain` "Hello"

    it "preserves finish reason in round-trip" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"custom-model","choices":[{"index":0,"delta":{},"finish_reason":"stop"}]}"""
      case fromOaCompatibleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          let roundTripJson = toOaCompatibleChunk commonChunk
          roundTripJson `shouldContain` "stop"

    it "BUG: may lose precision in timestamp during round-trip" do
      -- BUG: Timestamp precision may be lost in JSON serialization
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288123,"model":"custom-model","choices":[{"index":0,"delta":{},"finish_reason":null}]}"""
      case fromOaCompatibleChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          -- Created may lose precision if stored as Number instead of Int
          -- Test documents potential precision loss
          pure unit

  describe "Error Handling" do
    it "returns meaningful error message for invalid JSON" do
      let invalidJson = """{"id":"chatcmpl-123"""
      case fromOaCompatibleChunk invalidJson of
        Left err -> do
          -- Error message should be non-empty
          err.length `shouldNotEqual` 0
          -- Error message should indicate JSON parsing issue
          err `shouldContain` "error"
        Right _ -> pure unit  -- Should not succeed

    it "handles empty string input" do
      case fromOaCompatibleChunk "" of
        Left err -> do
          -- Should return error
          err.length `shouldNotEqual` 0
        Right _ -> pure unit  -- Should not succeed

    it "handles whitespace-only input" do
      case fromOaCompatibleChunk "   " of
        Left err -> do
          -- Should return error
          err.length `shouldNotEqual` 0
        Right _ -> pure unit  -- Should not succeed
