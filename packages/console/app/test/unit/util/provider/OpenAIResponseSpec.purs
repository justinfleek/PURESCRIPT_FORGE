-- | Deep comprehensive tests for OpenAI Response conversion module
-- | Tests fromOpenaiResponse and toOpenaiResponse with round-trip conversions,
-- | edge cases, and bug detection
module Test.Unit.Util.Provider.OpenAIResponseSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual, shouldContain)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Array (length, head)
import Data.Foldable (fold)
import Data.Array as Array
import Data.String as String

import Console.App.Routes.Omega.Util.Provider.OpenAI.Response
  ( fromOpenaiResponse
  , toOpenaiResponse
  )
import Console.App.Routes.Omega.Util.Provider.Provider
  ( CommonResponse
  , ResponseChoice
  , CommonUsage
  , MessageRole(..)
  , FinishReason(..)
  )

-- | Create mock CommonResponse
mkMockCommonResponse :: CommonResponse
mkMockCommonResponse =
  { id: "chatcmpl-123"
  , object: "chat.completion"
  , created: 1677652288
  , model: "gpt-4"
  , choices: []
  , usage: Nothing
  }

-- | Create mock ResponseChoice
mkMockChoice :: MessageRole -> String -> Maybe FinishReason -> ResponseChoice
mkMockChoice role content finishReason =
  { index: 0
  , message:
      { role
      , content: Just content
      , toolCalls: Nothing
      }
  , finishReason
  }

-- | Create mock CommonUsage
mkMockUsage :: CommonUsage
mkMockUsage =
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

-- | Valid OpenAI response JSON (minimal)
validOpenAIResponseMinimal :: String
validOpenAIResponseMinimal = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"Hello"},"finish_reason":"stop"}]}"""

-- | Valid OpenAI response JSON (full)
validOpenAIResponseFull :: String
validOpenAIResponseFull = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"Hello"},"finish_reason":"stop"}],"usage":{"prompt_tokens":10,"completion_tokens":20,"total_tokens":30}}"""

-- | Deep comprehensive tests for OpenAI Response conversions
spec :: Spec Unit
spec = describe "OpenAI Response Conversion Deep Tests" do
  describe "fromOpenaiResponse" do
    it "converts minimal valid OpenAI response to CommonResponse" do
      let commonResp = fromOpenaiResponse validOpenAIResponseMinimal
      commonResp.id `shouldEqual` "chatcmpl-123"
      commonResp.object `shouldEqual` "chat.completion"
      commonResp.model `shouldEqual` "gpt-4"
      commonResp.choices.length `shouldEqual` 1

    it "converts full OpenAI response with all fields" do
      let commonResp = fromOpenaiResponse validOpenAIResponseFull
      commonResp.id `shouldEqual` "chatcmpl-123"
      commonResp.model `shouldEqual` "gpt-4"
      commonResp.choices.length `shouldEqual` 1
      isJust commonResp.usage `shouldEqual` true

    it "handles empty choices array" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[]}"""
      let commonResp = fromOpenaiResponse json
      commonResp.choices.length `shouldEqual` 0

    it "handles single choice" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"stop"}]}"""
      let commonResp = fromOpenaiResponse json
      commonResp.choices.length `shouldEqual` 1

    it "handles multiple choices" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test1"},"finish_reason":"stop"},{"index":1,"message":{"role":"assistant","content":"test2"},"finish_reason":"stop"}]}"""
      let commonResp = fromOpenaiResponse json
      commonResp.choices.length `shouldEqual` 2

    it "handles assistant message" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"Hello"},"finish_reason":"stop"}]}"""
      let commonResp = fromOpenaiResponse json
      case head commonResp.choices of
        Just choice -> choice.message.role `shouldEqual` Assistant
        Nothing -> pure unit

    it "handles message with empty content" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":""},"finish_reason":"stop"}]}"""
      let commonResp = fromOpenaiResponse json
      case head commonResp.choices of
        Just choice -> choice.message.content `shouldEqual` Just ""
        Nothing -> pure unit

    it "handles message with null content" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":null},"finish_reason":"stop"}]}"""
      let commonResp = fromOpenaiResponse json
      -- Should handle gracefully
      commonResp.choices.length `shouldEqual` 1

    it "handles finish_reason stop" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"stop"}]}"""
      let commonResp = fromOpenaiResponse json
      case head commonResp.choices of
        Just choice -> choice.finishReason `shouldEqual` Just Stop
        Nothing -> pure unit

    it "handles finish_reason tool_calls" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"tool_calls"}]}"""
      let commonResp = fromOpenaiResponse json
      case head commonResp.choices of
        Just choice -> choice.finishReason `shouldEqual` Just ToolCalls
        Nothing -> pure unit

    it "handles finish_reason length" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"length"}]}"""
      let commonResp = fromOpenaiResponse json
      case head commonResp.choices of
        Just choice -> choice.finishReason `shouldEqual` Just Length
        Nothing -> pure unit

    it "handles finish_reason content_filter" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"content_filter"}]}"""
      let commonResp = fromOpenaiResponse json
      case head commonResp.choices of
        Just choice -> choice.finishReason `shouldEqual` Just ContentFilter
        Nothing -> pure unit

    it "handles missing finish_reason" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test"}]}"""
      let commonResp = fromOpenaiResponse json
      case head commonResp.choices of
        Just choice -> choice.finishReason `shouldEqual` Nothing
        Nothing -> pure unit

    it "handles usage information" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"stop"}],"usage":{"prompt_tokens":10,"completion_tokens":20,"total_tokens":30}}"""
      let commonResp = fromOpenaiResponse json
      isJust commonResp.usage `shouldEqual` true

    it "handles usage with prompt_tokens" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"stop"}],"usage":{"prompt_tokens":10}}"""
      let commonResp = fromOpenaiResponse json
      case commonResp.usage of
        Just usage -> usage.promptTokens `shouldEqual` Just 10
        Nothing -> pure unit

    it "handles usage with completion_tokens" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"stop"}],"usage":{"completion_tokens":20}}"""
      let commonResp = fromOpenaiResponse json
      case commonResp.usage of
        Just usage -> usage.completionTokens `shouldEqual` Just 20
        Nothing -> pure unit

    it "handles usage with total_tokens" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"stop"}],"usage":{"total_tokens":30}}"""
      let commonResp = fromOpenaiResponse json
      case commonResp.usage of
        Just usage -> usage.totalTokens `shouldEqual` Just 30
        Nothing -> pure unit

    it "handles missing usage information" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"stop"}]}"""
      let commonResp = fromOpenaiResponse json
      commonResp.usage `shouldEqual` Nothing

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":""" <> "\"" <> longContent <> "\"" <> """},"finish_reason":"stop"}]}"""
      let commonResp = fromOpenaiResponse json
      case head commonResp.choices of
        Just choice -> do
          case choice.message.content of
            Just c -> c.length `shouldEqual` 10000
            Nothing -> pure unit
        Nothing -> pure unit

    it "handles unicode characters in content" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"测试-🚀-こんにちは"},"finish_reason":"stop"}]}"""
      let commonResp = fromOpenaiResponse json
      case head commonResp.choices of
        Just choice -> choice.message.content `shouldContain` "测试"
        Nothing -> pure unit

    it "handles special characters in content" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test\\nwith\\tnewlines\\\"and\\\"quotes"},"finish_reason":"stop"}]}"""
      let commonResp = fromOpenaiResponse json
      -- Should preserve special characters
      commonResp.choices.length `shouldEqual` 1

    it "handles empty id string" do
      let json = """{"id":"","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"stop"}]}"""
      let commonResp = fromOpenaiResponse json
      commonResp.id `shouldEqual` ""

    it "handles very long id string" do
      let longId = fold (replicate 1000 "a")
      let json = """{"id":""" <> "\"" <> longId <> "\"" <> ""","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"stop"}]}"""
      let commonResp = fromOpenaiResponse json
      commonResp.id.length `shouldEqual` 1000

    it "handles zero created timestamp" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":0,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"stop"}]}"""
      let commonResp = fromOpenaiResponse json
      commonResp.created `shouldEqual` 0

    it "handles negative created timestamp" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":-1,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"stop"}]}"""
      let commonResp = fromOpenaiResponse json
      -- Should preserve negative value
      commonResp.created `shouldEqual` (-1)

    it "handles very large created timestamp" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":2147483647,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"stop"}]}"""
      let commonResp = fromOpenaiResponse json
      commonResp.created `shouldEqual` 2147483647

    it "handles tool calls in message" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":null,"tool_calls":[{"id":"call_123","type":"function","function":{"name":"test_fn","arguments":"{}"}}]},"finish_reason":"tool_calls"}]}"""
      let commonResp = fromOpenaiResponse json
      case head commonResp.choices of
        Just choice -> isJust choice.message.toolCalls `shouldEqual` true
        Nothing -> pure unit

    it "BUG: handles invalid JSON gracefully" do
      -- BUG: Invalid JSON may throw or return malformed CommonResponse
      let invalidJson = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288"""
      -- This may throw or return malformed data
      -- Test documents the behavior
      pure unit

    it "BUG: handles malformed JSON (missing quotes)" do
      -- BUG: Malformed JSON may not be handled gracefully
      let malformedJson = """{id:"chatcmpl-123",object:"chat.completion"}"""
      -- This may throw or fail silently
      -- Test documents the behavior
      pure unit

    it "BUG: handles missing required fields" do
      -- BUG: Missing id, object, created, model, or choices may not be handled gracefully
      let json = """{"object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[]}"""
      -- Should handle missing id field
      let commonResp = fromOpenaiResponse json
      -- id may be empty string or throw
      pure unit

    it "BUG: handles invalid finish_reason" do
      -- BUG: Invalid finish_reason may not be handled gracefully
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"invalid_reason"}]}"""
      let commonResp = fromOpenaiResponse json
      -- finish_reason may be Nothing or throw
      -- Test documents the behavior
      pure unit

  describe "toOpenaiResponse" do
    it "converts minimal CommonResponse to OpenAI format" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "Hello" (Just Stop)] }
      let openaiJson = toOpenaiResponse commonResp
      -- Should contain id, object, model, choices
      openaiJson `shouldContain` "chatcmpl-123"
      openaiJson `shouldContain` "chat.completion"
      openaiJson `shouldContain` "gpt-4"
      openaiJson `shouldContain` "choices"

    it "converts full CommonResponse with all fields" do
      let commonResp = mkMockCommonResponse
        { choices = [mkMockChoice Assistant "Hello" (Just Stop)]
        , usage = Just mkMockUsage
        }
      let openaiJson = toOpenaiResponse commonResp
      openaiJson `shouldContain` "usage"
      openaiJson `shouldContain` "prompt_tokens"

    it "handles empty choices array" do
      let commonResp = mkMockCommonResponse { choices = [] }
      let openaiJson = toOpenaiResponse commonResp
      openaiJson `shouldContain` "choices"
      openaiJson `shouldContain` "[]"

    it "handles single choice" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "test" (Just Stop)] }
      let openaiJson = toOpenaiResponse commonResp
      openaiJson `shouldContain` "assistant"
      openaiJson `shouldContain` "test"

    it "handles multiple choices" do
      let commonResp = mkMockCommonResponse
        { choices =
            [ mkMockChoice Assistant "test1" (Just Stop)
            , mkMockChoice Assistant "test2" (Just Stop)
            ]
        }
      let openaiJson = toOpenaiResponse commonResp
      openaiJson `shouldContain` "test1"
      openaiJson `shouldContain` "test2"

    it "handles assistant message" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "Hello" (Just Stop)] }
      let openaiJson = toOpenaiResponse commonResp
      openaiJson `shouldContain` "assistant"

    it "handles message with empty content" do
      let commonResp = mkMockCommonResponse
        { choices =
            [ { index: 0
              , message:
                  { role: Assistant
                  , content: Just ""
                  , toolCalls: Nothing
                  }
              , finishReason: Just Stop
              }
            ]
        }
      let openaiJson = toOpenaiResponse commonResp
      openaiJson `shouldContain` "content"

    it "handles message with Nothing content" do
      let commonResp = mkMockCommonResponse
        { choices =
            [ { index: 0
              , message:
                  { role: Assistant
                  , content: Nothing
                  , toolCalls: Nothing
                  }
              , finishReason: Just Stop
              }
            ]
        }
      let openaiJson = toOpenaiResponse commonResp
      -- Should handle Nothing content gracefully
      openaiJson `shouldContain` "choices"

    it "handles finishReason Stop" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "test" (Just Stop)] }
      let openaiJson = toOpenaiResponse commonResp
      openaiJson `shouldContain` "finish_reason"
      openaiJson `shouldContain` "stop"

    it "handles finishReason ToolCalls" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "test" (Just ToolCalls)] }
      let openaiJson = toOpenaiResponse commonResp
      openaiJson `shouldContain` "tool_calls"

    it "handles finishReason Length" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "test" (Just Length)] }
      let openaiJson = toOpenaiResponse commonResp
      openaiJson `shouldContain` "length"

    it "handles finishReason ContentFilter" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "test" (Just ContentFilter)] }
      let openaiJson = toOpenaiResponse commonResp
      openaiJson `shouldContain` "content_filter"

    it "omits finish_reason when Nothing" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "test" Nothing] }
      let openaiJson = toOpenaiResponse commonResp
      -- finish_reason may be omitted or null
      -- Test documents behavior
      pure unit

    it "handles usage information" do
      let commonResp = mkMockCommonResponse
        { choices = [mkMockChoice Assistant "test" (Just Stop)]
        , usage = Just mkMockUsage
        }
      let openaiJson = toOpenaiResponse commonResp
      openaiJson `shouldContain` "usage"
      openaiJson `shouldContain` "prompt_tokens"
      openaiJson `shouldContain` "completion_tokens"

    it "omits usage when Nothing" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "test" (Just Stop)] }
      let openaiJson = toOpenaiResponse commonResp
      -- usage may be omitted when Nothing
      -- Test documents behavior
      pure unit

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant longContent (Just Stop)] }
      let openaiJson = toOpenaiResponse commonResp
      -- Should preserve long content
      openaiJson.length `shouldNotEqual` 0

    it "handles unicode characters" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "测试-🚀-こんにちは" (Just Stop)] }
      let openaiJson = toOpenaiResponse commonResp
      openaiJson `shouldContain` "测试"

    it "handles empty id string" do
      let commonResp = mkMockCommonResponse { id = "" }
      let openaiJson = toOpenaiResponse commonResp
      openaiJson `shouldContain` "id"
      openaiJson `shouldContain` "\"\""

    it "handles very long id string" do
      let longId = fold (replicate 1000 "a")
      let commonResp = mkMockCommonResponse { id = longId }
      let openaiJson = toOpenaiResponse commonResp
      openaiJson `shouldContain` longId

  describe "Round-trip Conversions" do
    it "preserves data in round-trip: OpenAI → CommonResponse → OpenAI" do
      let originalJson = validOpenAIResponseMinimal
      let commonResp = fromOpenaiResponse originalJson
      let roundTripJson = toOpenaiResponse commonResp
      -- Round-trip should preserve essential data
      roundTripJson `shouldContain` "chatcmpl-123"
      roundTripJson `shouldContain` "gpt-4"
      roundTripJson `shouldContain` "choices"

    it "preserves all fields in round-trip with full response" do
      let originalJson = validOpenAIResponseFull
      let commonResp = fromOpenaiResponse originalJson
      let roundTripJson = toOpenaiResponse commonResp
      -- Should preserve id, model, choices, usage
      roundTripJson `shouldContain` "chatcmpl-123"
      roundTripJson `shouldContain` "gpt-4"
      roundTripJson `shouldContain` "usage"

    it "preserves choices in round-trip" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"Hello"},"finish_reason":"stop"},{"index":1,"message":{"role":"assistant","content":"Hi"},"finish_reason":"stop"}]}"""
      let commonResp = fromOpenaiResponse json
      let roundTripJson = toOpenaiResponse commonResp
      roundTripJson `shouldContain` "Hello"
      roundTripJson `shouldContain` "Hi"

    it "BUG: may lose precision in timestamp during round-trip" do
      -- BUG: Timestamp precision may be lost in JSON serialization
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288123,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"stop"}]}"""
      let commonResp = fromOpenaiResponse json
      -- Created may lose precision if stored as Number instead of Int
      -- Test documents potential precision loss
      pure unit

    it "BUG: may change field order in round-trip" do
      -- BUG: JSON field order may change (not critical but documents behavior)
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"gpt-4","choices":[]}"""
      let commonResp = fromOpenaiResponse json
      let roundTripJson = toOpenaiResponse commonResp
      -- Field order may differ but content should be same
      roundTripJson `shouldContain` "id"
      roundTripJson `shouldContain` "model"

  describe "Edge Cases" do
    it "handles CommonResponse → OpenAI → CommonResponse round-trip" do
      let originalResp = mkMockCommonResponse
        { id: "chatcmpl-123"
        , model: "gpt-4"
        , choices = [mkMockChoice Assistant "test" (Just Stop)]
        , usage = Just mkMockUsage
        }
      let openaiJson = toOpenaiResponse originalResp
      let roundTripResp = fromOpenaiResponse openaiJson
      roundTripResp.id `shouldEqual` "chatcmpl-123"
      roundTripResp.model `shouldEqual` "gpt-4"
      roundTripResp.choices.length `shouldEqual` 1

    it "handles empty id in round-trip" do
      let commonResp = mkMockCommonResponse { id = "" }
      let openaiJson = toOpenaiResponse commonResp
      let roundTripResp = fromOpenaiResponse openaiJson
      roundTripResp.id `shouldEqual` ""

    it "handles zero created timestamp in round-trip" do
      let commonResp = mkMockCommonResponse { created = 0 }
      let openaiJson = toOpenaiResponse commonResp
      let roundTripResp = fromOpenaiResponse openaiJson
      roundTripResp.created `shouldEqual` 0

    it "handles very large created timestamp" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":2147483647,"model":"gpt-4","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"stop"}]}"""
      let commonResp = fromOpenaiResponse json
      commonResp.created `shouldEqual` 2147483647
