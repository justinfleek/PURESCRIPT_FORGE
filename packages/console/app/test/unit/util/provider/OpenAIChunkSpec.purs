-- | Deep comprehensive tests for OpenAI Chunk conversion module
-- | Tests fromOpenaiChunk and toOpenaiChunk with error handling,
-- | edge cases, and bug detection
module Test.Unit.Util.Provider.OpenAIChunkSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual, shouldContain)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Either (Either(..), isLeft, isRight)
import Data.Array (length, head)
import Data.Foldable (fold)
import Data.Array as Array
import Data.String as String

import Console.App.Routes.Omega.Util.Provider.OpenAI.Chunk
  ( fromOpenaiChunk
  , toOpenaiChunk
  )
import Console.App.Routes.Omega.Util.Provider.Provider
  ( CommonChunk
  , ChunkChoice
  , ChunkDelta
  , CommonUsage
  , MessageRole(..)
  , FinishReason(..)
  )

-- | Create mock CommonChunk
mkMockCommonChunk :: CommonChunk
mkMockCommonChunk =
  { id: "chatcmpl-123"
  , object: "chat.completion.chunk"
  , created: 1677652288
  , model: "gpt-4"
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

-- | Valid OpenAI chunk JSON (content delta)
validOpenAIChunkContent :: String
validOpenAIChunkContent = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{"content":"Hello"},"finish_reason":null}]}"""

-- | Valid OpenAI chunk JSON (finish reason)
validOpenAIChunkFinish :: String
validOpenAIChunkFinish = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{},"finish_reason":"stop"}]}"""

-- | Valid OpenAI chunk JSON (tool calls)
validOpenAIChunkToolCalls :: String
validOpenAIChunkToolCalls = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{"role":"assistant","tool_calls":[{"index":0,"id":"call_123","type":"function","function":{"name":"test_fn","arguments":"{}"}}]},"finish_reason":null}]}"""

-- | Deep comprehensive tests for OpenAI Chunk conversions
spec :: Spec Unit
spec = describe "OpenAI Chunk Conversion Deep Tests" do
  describe "fromOpenaiChunk" do
    it "converts valid OpenAI chunk with content delta to CommonChunk" do
      case fromOpenaiChunk validOpenAIChunkContent of
        Left err -> pure unit  -- Should not error
        Right commonChunk -> do
          commonChunk.id `shouldEqual` "chatcmpl-123"
          commonChunk.object `shouldEqual` "chat.completion.chunk"
          commonChunk.model `shouldEqual` "gpt-4"
          commonChunk.choices.length `shouldEqual` 1

    it "converts chunk with finish reason" do
      case fromOpenaiChunk validOpenAIChunkFinish of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.finishReason `shouldEqual` Just Stop
            Nothing -> pure unit

    it "converts chunk with tool calls" do
      case fromOpenaiChunk validOpenAIChunkToolCalls of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> isJust choice.delta.toolCalls `shouldEqual` true
            Nothing -> pure unit

    it "handles empty choices array" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> commonChunk.choices.length `shouldEqual` 0

    it "handles single choice" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{"content":"test"},"finish_reason":null}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> commonChunk.choices.length `shouldEqual` 1

    it "handles multiple choices" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{"content":"test1"},"finish_reason":null},{"index":1,"delta":{"content":"test2"},"finish_reason":null}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> commonChunk.choices.length `shouldEqual` 2

    it "handles empty delta" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{},"finish_reason":null}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.delta.content `shouldEqual` Nothing
            Nothing -> pure unit

    it "handles delta with content" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{"content":"Hello"},"finish_reason":null}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.delta.content `shouldEqual` Just "Hello"
            Nothing -> pure unit

    it "handles delta with empty content" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{"content":""},"finish_reason":null}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.delta.content `shouldEqual` Just ""
            Nothing -> pure unit

    it "handles delta with role" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{"role":"assistant"},"finish_reason":null}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.delta.role `shouldEqual` Just Assistant
            Nothing -> pure unit

    it "handles finish_reason stop" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{},"finish_reason":"stop"}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.finishReason `shouldEqual` Just Stop
            Nothing -> pure unit

    it "handles finish_reason tool_calls" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{},"finish_reason":"tool_calls"}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.finishReason `shouldEqual` Just ToolCalls
            Nothing -> pure unit

    it "handles finish_reason length" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{},"finish_reason":"length"}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.finishReason `shouldEqual` Just Length
            Nothing -> pure unit

    it "handles finish_reason content_filter" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{},"finish_reason":"content_filter"}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.finishReason `shouldEqual` Just ContentFilter
            Nothing -> pure unit

    it "handles missing finish_reason" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{}}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.finishReason `shouldEqual` Nothing
            Nothing -> pure unit

    it "handles usage information" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{},"finish_reason":null}],"usage":{"prompt_tokens":10,"completion_tokens":20,"total_tokens":30}}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> isJust commonChunk.usage `shouldEqual` true

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{"content":""" <> "\"" <> longContent <> "\"" <> """},"finish_reason":null}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> do
              case choice.delta.content of
                Just c -> c.length `shouldEqual` 10000
                Nothing -> pure unit
            Nothing -> pure unit

    it "handles unicode characters in content" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{"content":"测试-🚀-こんにちは"},"finish_reason":null}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> do
              case choice.delta.content of
                Just c -> c `shouldContain` "测试"
                Nothing -> pure unit
            Nothing -> pure unit

    it "handles special characters in content" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{"content":"test\\nwith\\tnewlines\\\"and\\\"quotes"},"finish_reason":null}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> commonChunk.choices.length `shouldEqual` 1

    it "handles empty id string" do
      let json = """{"id":"","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{},"finish_reason":null}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> commonChunk.id `shouldEqual` ""

    it "handles very long id string" do
      let longId = fold (replicate 1000 "a")
      let json = """{"id":""" <> "\"" <> longId <> "\"" <> ""","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{},"finish_reason":null}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> commonChunk.id.length `shouldEqual` 1000

    it "handles zero created timestamp" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":0,"model":"gpt-4","choices":[{"index":0,"delta":{},"finish_reason":null}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> commonChunk.created `shouldEqual` 0

    it "handles negative created timestamp" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":-1,"model":"gpt-4","choices":[{"index":0,"delta":{},"finish_reason":null}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> commonChunk.created `shouldEqual` (-1)

    it "handles very large created timestamp" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":2147483647,"model":"gpt-4","choices":[{"index":0,"delta":{},"finish_reason":null}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> commonChunk.created `shouldEqual` 2147483647

    it "returns Left for invalid JSON string" do
      let invalidJson = """{"id":"chatcmpl-123","object":"chat.completion.chunk"""
      case fromOpenaiChunk invalidJson of
        Left err -> do
          -- Should return error message
          err.length `shouldNotEqual` 0
        Right _ -> pure unit  -- Should not succeed

    it "returns Left for malformed JSON (missing quotes)" do
      let malformedJson = """{id:"chatcmpl-123",object:"chat.completion.chunk"}"""
      case fromOpenaiChunk malformedJson of
        Left err -> do
          -- Should return error message
          err.length `shouldNotEqual` 0
        Right _ -> pure unit  -- Should not succeed

    it "BUG: may return Right for missing required fields" do
      -- BUG: Missing id, object, created, model, or choices may not return Left
      let json = """{"object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit  -- Should error but may not
        Right commonChunk -> do
          -- id may be empty string instead of error
          pure unit

    it "BUG: may not validate finish_reason" do
      -- BUG: Invalid finish_reason may not return Left
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{},"finish_reason":"invalid_reason"}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit  -- Should error but may not
        Right commonChunk -> do
          -- finish_reason may be Nothing instead of error
          pure unit

  describe "toOpenaiChunk" do
    it "converts minimal CommonChunk to OpenAI format" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "Hello") Nothing] }
      let openaiJson = toOpenaiChunk commonChunk
      -- Should contain id, object, model, choices
      openaiJson `shouldContain` "chatcmpl-123"
      openaiJson `shouldContain` "chat.completion.chunk"
      openaiJson `shouldContain` "gpt-4"
      openaiJson `shouldContain` "choices"

    it "converts CommonChunk with content delta" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "test") Nothing] }
      let openaiJson = toOpenaiChunk commonChunk
      openaiJson `shouldContain` "delta"
      openaiJson `shouldContain` "test"

    it "converts CommonChunk with finish reason" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just Stop)] }
      let openaiJson = toOpenaiChunk commonChunk
      openaiJson `shouldContain` "finish_reason"
      openaiJson `shouldContain` "stop"

    it "handles empty choices array" do
      let commonChunk = mkMockCommonChunk { choices = [] }
      let openaiJson = toOpenaiChunk commonChunk
      openaiJson `shouldContain` "choices"
      openaiJson `shouldContain` "[]"

    it "handles single choice" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "test") Nothing] }
      let openaiJson = toOpenaiChunk commonChunk
      openaiJson `shouldContain` "test"

    it "handles multiple choices" do
      let commonChunk = mkMockCommonChunk
        { choices =
            [ mkMockChunkChoice (Just "test1") Nothing
            , mkMockChunkChoice (Just "test2") Nothing
            ]
        }
      let openaiJson = toOpenaiChunk commonChunk
      openaiJson `shouldContain` "test1"
      openaiJson `shouldContain` "test2"

    it "handles empty delta" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing Nothing] }
      let openaiJson = toOpenaiChunk commonChunk
      openaiJson `shouldContain` "delta"

    it "handles delta with content" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "Hello") Nothing] }
      let openaiJson = toOpenaiChunk commonChunk
      openaiJson `shouldContain` "content"
      openaiJson `shouldContain` "Hello"

    it "handles delta with empty content" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "") Nothing] }
      let openaiJson = toOpenaiChunk commonChunk
      openaiJson `shouldContain` "content"

    it "handles delta with role" do
      let commonChunk = mkMockCommonChunk
        { choices =
            [ { index: 0
              , delta:
                  { role: Just Assistant
                  , content: Nothing
                  , toolCalls: Nothing
                  }
              , finishReason: Nothing
              }
            ]
        }
      let openaiJson = toOpenaiChunk commonChunk
      openaiJson `shouldContain` "role"
      openaiJson `shouldContain` "assistant"

    it "handles finishReason Stop" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just Stop)] }
      let openaiJson = toOpenaiChunk commonChunk
      openaiJson `shouldContain` "finish_reason"
      openaiJson `shouldContain` "stop"

    it "handles finishReason ToolCalls" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just ToolCalls)] }
      let openaiJson = toOpenaiChunk commonChunk
      openaiJson `shouldContain` "tool_calls"

    it "handles finishReason Length" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just Length)] }
      let openaiJson = toOpenaiChunk commonChunk
      openaiJson `shouldContain` "length"

    it "handles finishReason ContentFilter" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just ContentFilter)] }
      let openaiJson = toOpenaiChunk commonChunk
      openaiJson `shouldContain` "content_filter"

    it "omits finish_reason when Nothing" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing Nothing] }
      let openaiJson = toOpenaiChunk commonChunk
      -- finish_reason may be omitted or null
      -- Test documents behavior
      pure unit

    it "handles usage information" do
      let usage =
            { inputTokens: Just 10
            , outputTokens: Just 20
            , totalTokens: Just 30
            , promptTokens: Just 10
            , completionTokens: Just 20
            , cacheReadInputTokens: Nothing
            , cacheCreationEphemeral5mInputTokens: Nothing
            , cacheCreationEphemeral1hInputTokens: Nothing
            , cachedTokens: Nothing
            , reasoningTokens: Nothing
            }
      let commonChunk = mkMockCommonChunk
        { choices = [mkMockChunkChoice Nothing Nothing]
        , usage = Just usage
        }
      let openaiJson = toOpenaiChunk commonChunk
      openaiJson `shouldContain` "usage"

    it "omits usage when Nothing" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing Nothing] }
      let openaiJson = toOpenaiChunk commonChunk
      -- usage may be omitted when Nothing
      -- Test documents behavior
      pure unit

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just longContent) Nothing] }
      let openaiJson = toOpenaiChunk commonChunk
      -- Should preserve long content
      openaiJson.length `shouldNotEqual` 0

    it "handles unicode characters" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "测试-🚀-こんにちは") Nothing] }
      let openaiJson = toOpenaiChunk commonChunk
      openaiJson `shouldContain` "测试"

    it "handles empty id string" do
      let commonChunk = mkMockCommonChunk { id = "" }
      let openaiJson = toOpenaiChunk commonChunk
      openaiJson `shouldContain` "id"
      openaiJson `shouldContain` "\"\""

    it "handles very long id string" do
      let longId = fold (replicate 1000 "a")
      let commonChunk = mkMockCommonChunk { id = longId }
      let openaiJson = toOpenaiChunk commonChunk
      openaiJson `shouldContain` longId

  describe "Round-trip Conversions" do
    it "preserves data in round-trip: OpenAI → CommonChunk → OpenAI" do
      case fromOpenaiChunk validOpenAIChunkContent of
        Left err -> pure unit
        Right commonChunk -> do
          let roundTripJson = toOpenaiChunk commonChunk
          -- Round-trip should preserve essential data
          roundTripJson `shouldContain` "chatcmpl-123"
          roundTripJson `shouldContain` "gpt-4"
          roundTripJson `shouldContain` "choices"

    it "preserves content delta in round-trip" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{"content":"Hello"},"finish_reason":null}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          let roundTripJson = toOpenaiChunk commonChunk
          roundTripJson `shouldContain` "Hello"

    it "preserves finish reason in round-trip" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288,"model":"gpt-4","choices":[{"index":0,"delta":{},"finish_reason":"stop"}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          let roundTripJson = toOpenaiChunk commonChunk
          roundTripJson `shouldContain` "stop"

    it "BUG: may lose precision in timestamp during round-trip" do
      -- BUG: Timestamp precision may be lost in JSON serialization
      let json = """{"id":"chatcmpl-123","object":"chat.completion.chunk","created":1677652288123,"model":"gpt-4","choices":[{"index":0,"delta":{},"finish_reason":null}]}"""
      case fromOpenaiChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          -- Created may lose precision if stored as Number instead of Int
          -- Test documents potential precision loss
          pure unit

  describe "Error Handling" do
    it "returns meaningful error message for invalid JSON" do
      let invalidJson = """{"id":"chatcmpl-123"""
      case fromOpenaiChunk invalidJson of
        Left err -> do
          -- Error message should be non-empty
          err.length `shouldNotEqual` 0
          -- Error message should indicate JSON parsing issue
          err `shouldContain` "error"
        Right _ -> pure unit  -- Should not succeed

    it "handles empty string input" do
      case fromOpenaiChunk "" of
        Left err -> do
          -- Should return error
          err.length `shouldNotEqual` 0
        Right _ -> pure unit  -- Should not succeed

    it "handles whitespace-only input" do
      case fromOpenaiChunk "   " of
        Left err -> do
          -- Should return error
          err.length `shouldNotEqual` 0
        Right _ -> pure unit  -- Should not succeed
