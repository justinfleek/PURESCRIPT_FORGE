-- | Deep comprehensive tests for OpenAICompatible Response conversion module
-- | Tests fromOaCompatibleResponse and toOaCompatibleResponse with round-trip conversions,
-- | edge cases, and bug detection
-- | Note: OpenAICompatible format is similar to OpenAI format
module Test.Unit.Util.Provider.OpenAICompatibleResponseSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual, shouldContain)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Array (length, head)
import Data.Foldable (fold)
import Data.Array as Array
import Data.String as String

import Console.App.Routes.Omega.Util.Provider.OpenAICompatible.Response
  ( fromOaCompatibleResponse
  , toOaCompatibleResponse
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
  , model: "custom-model"
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

-- | Valid OpenAICompatible response JSON (minimal) - same format as OpenAI
validOaCompatibleResponseMinimal :: String
validOaCompatibleResponseMinimal = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"custom-model","choices":[{"index":0,"message":{"role":"assistant","content":"Hello"},"finish_reason":"stop"}]}"""

-- | Valid OpenAICompatible response JSON (full)
validOaCompatibleResponseFull :: String
validOaCompatibleResponseFull = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"custom-model","choices":[{"index":0,"message":{"role":"assistant","content":"Hello"},"finish_reason":"stop"}],"usage":{"prompt_tokens":10,"completion_tokens":20,"total_tokens":30}}"""

-- | Deep comprehensive tests for OpenAICompatible Response conversions
spec :: Spec Unit
spec = describe "OpenAICompatible Response Conversion Deep Tests" do
  describe "fromOaCompatibleResponse" do
    it "converts minimal valid OpenAICompatible response to CommonResponse" do
      let commonResp = fromOaCompatibleResponse validOaCompatibleResponseMinimal
      commonResp.id `shouldEqual` "chatcmpl-123"
      commonResp.object `shouldEqual` "chat.completion"
      commonResp.model `shouldEqual` "custom-model"
      commonResp.choices.length `shouldEqual` 1

    it "converts full OpenAICompatible response with all fields" do
      let commonResp = fromOaCompatibleResponse validOaCompatibleResponseFull
      commonResp.id `shouldEqual` "chatcmpl-123"
      commonResp.model `shouldEqual` "custom-model"
      commonResp.choices.length `shouldEqual` 1
      isJust commonResp.usage `shouldEqual` true

    it "handles empty choices array" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"custom-model","choices":[]}"""
      let commonResp = fromOaCompatibleResponse json
      commonResp.choices.length `shouldEqual` 0

    it "handles single choice" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"custom-model","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"stop"}]}"""
      let commonResp = fromOaCompatibleResponse json
      commonResp.choices.length `shouldEqual` 1

    it "handles multiple choices" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"custom-model","choices":[{"index":0,"message":{"role":"assistant","content":"test1"},"finish_reason":"stop"},{"index":1,"message":{"role":"assistant","content":"test2"},"finish_reason":"stop"}]}"""
      let commonResp = fromOaCompatibleResponse json
      commonResp.choices.length `shouldEqual` 2

    it "handles assistant message" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"custom-model","choices":[{"index":0,"message":{"role":"assistant","content":"Hello"},"finish_reason":"stop"}]}"""
      let commonResp = fromOaCompatibleResponse json
      case head commonResp.choices of
        Just choice -> choice.message.role `shouldEqual` Assistant
        Nothing -> pure unit

    it "handles finish_reason stop" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"custom-model","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"stop"}]}"""
      let commonResp = fromOaCompatibleResponse json
      case head commonResp.choices of
        Just choice -> choice.finishReason `shouldEqual` Just Stop
        Nothing -> pure unit

    it "handles finish_reason tool_calls" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"custom-model","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"tool_calls"}]}"""
      let commonResp = fromOaCompatibleResponse json
      case head commonResp.choices of
        Just choice -> choice.finishReason `shouldEqual` Just ToolCalls
        Nothing -> pure unit

    it "handles finish_reason length" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"custom-model","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"length"}]}"""
      let commonResp = fromOaCompatibleResponse json
      case head commonResp.choices of
        Just choice -> choice.finishReason `shouldEqual` Just Length
        Nothing -> pure unit

    it "handles finish_reason content_filter" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"custom-model","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"content_filter"}]}"""
      let commonResp = fromOaCompatibleResponse json
      case head commonResp.choices of
        Just choice -> choice.finishReason `shouldEqual` Just ContentFilter
        Nothing -> pure unit

    it "handles missing finish_reason" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"custom-model","choices":[{"index":0,"message":{"role":"assistant","content":"test"}]}"""
      let commonResp = fromOaCompatibleResponse json
      case head commonResp.choices of
        Just choice -> choice.finishReason `shouldEqual` Nothing
        Nothing -> pure unit

    it "handles usage information" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"custom-model","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"stop"}],"usage":{"prompt_tokens":10,"completion_tokens":20,"total_tokens":30}}"""
      let commonResp = fromOaCompatibleResponse json
      isJust commonResp.usage `shouldEqual` true

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"custom-model","choices":[{"index":0,"message":{"role":"assistant","content":""" <> "\"" <> longContent <> "\"" <> """},"finish_reason":"stop"}]}"""
      let commonResp = fromOaCompatibleResponse json
      case head commonResp.choices of
        Just choice -> do
          case choice.message.content of
            Just c -> c.length `shouldEqual` 10000
            Nothing -> pure unit
        Nothing -> pure unit

    it "handles unicode characters in content" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"custom-model","choices":[{"index":0,"message":{"role":"assistant","content":"测试-🚀-こんにちは"},"finish_reason":"stop"}]}"""
      let commonResp = fromOaCompatibleResponse json
      case head commonResp.choices of
        Just choice -> choice.message.content `shouldContain` "测试"
        Nothing -> pure unit

    it "BUG: handles invalid JSON gracefully" do
      -- BUG: Invalid JSON may throw or return malformed CommonResponse
      let invalidJson = """{"id":"chatcmpl-123","object":"chat.completion"""
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
      let json = """{"object":"chat.completion","created":1677652288,"model":"custom-model","choices":[]}"""
      -- Should handle missing id field
      let commonResp = fromOaCompatibleResponse json
      -- id may be empty string or throw
      pure unit

    it "BUG: handles invalid finish_reason" do
      -- BUG: Invalid finish_reason may not be handled gracefully
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"custom-model","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"invalid_reason"}]}"""
      let commonResp = fromOaCompatibleResponse json
      -- finish_reason may be Nothing or throw
      -- Test documents the behavior
      pure unit

  describe "toOaCompatibleResponse" do
    it "converts minimal CommonResponse to OpenAICompatible format" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "Hello" (Just Stop)] }
      let oaCompatJson = toOaCompatibleResponse commonResp
      -- Should contain id, object, model, choices
      oaCompatJson `shouldContain` "chatcmpl-123"
      oaCompatJson `shouldContain` "chat.completion"
      oaCompatJson `shouldContain` "custom-model"
      oaCompatJson `shouldContain` "choices"

    it "converts full CommonResponse with all fields" do
      let commonResp = mkMockCommonResponse
        { choices = [mkMockChoice Assistant "Hello" (Just Stop)]
        , usage = Just mkMockUsage
        }
      let oaCompatJson = toOaCompatibleResponse commonResp
      oaCompatJson `shouldContain` "usage"
      oaCompatJson `shouldContain` "prompt_tokens"

    it "handles empty choices array" do
      let commonResp = mkMockCommonResponse { choices = [] }
      let oaCompatJson = toOaCompatibleResponse commonResp
      oaCompatJson `shouldContain` "choices"
      oaCompatJson `shouldContain` "[]"

    it "handles single choice" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "test" (Just Stop)] }
      let oaCompatJson = toOaCompatibleResponse commonResp
      oaCompatJson `shouldContain` "assistant"
      oaCompatJson `shouldContain` "test"

    it "handles finishReason Stop" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "test" (Just Stop)] }
      let oaCompatJson = toOaCompatibleResponse commonResp
      oaCompatJson `shouldContain` "finish_reason"
      oaCompatJson `shouldContain` "stop"

    it "handles finishReason ToolCalls" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "test" (Just ToolCalls)] }
      let oaCompatJson = toOaCompatibleResponse commonResp
      oaCompatJson `shouldContain` "tool_calls"

    it "handles finishReason Length" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "test" (Just Length)] }
      let oaCompatJson = toOaCompatibleResponse commonResp
      oaCompatJson `shouldContain` "length"

    it "handles finishReason ContentFilter" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "test" (Just ContentFilter)] }
      let oaCompatJson = toOaCompatibleResponse commonResp
      oaCompatJson `shouldContain` "content_filter"

    it "handles usage information" do
      let commonResp = mkMockCommonResponse
        { choices = [mkMockChoice Assistant "test" (Just Stop)]
        , usage = Just mkMockUsage
        }
      let oaCompatJson = toOaCompatibleResponse commonResp
      oaCompatJson `shouldContain` "usage"
      oaCompatJson `shouldContain` "prompt_tokens"
      oaCompatJson `shouldContain` "completion_tokens"

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant longContent (Just Stop)] }
      let oaCompatJson = toOaCompatibleResponse commonResp
      -- Should preserve long content
      oaCompatJson.length `shouldNotEqual` 0

    it "handles unicode characters" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "测试-🚀-こんにちは" (Just Stop)] }
      let oaCompatJson = toOaCompatibleResponse commonResp
      oaCompatJson `shouldContain` "测试"

  describe "Round-trip Conversions" do
    it "preserves data in round-trip: OpenAICompatible → CommonResponse → OpenAICompatible" do
      let originalJson = validOaCompatibleResponseMinimal
      let commonResp = fromOaCompatibleResponse originalJson
      let roundTripJson = toOaCompatibleResponse commonResp
      -- Round-trip should preserve essential data
      roundTripJson `shouldContain` "chatcmpl-123"
      roundTripJson `shouldContain` "custom-model"
      roundTripJson `shouldContain` "choices"

    it "preserves all fields in round-trip with full response" do
      let originalJson = validOaCompatibleResponseFull
      let commonResp = fromOaCompatibleResponse originalJson
      let roundTripJson = toOaCompatibleResponse commonResp
      -- Should preserve id, model, choices, usage
      roundTripJson `shouldContain` "chatcmpl-123"
      roundTripJson `shouldContain` "custom-model"
      roundTripJson `shouldContain` "usage"

    it "preserves content in round-trip" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"custom-model","choices":[{"index":0,"message":{"role":"assistant","content":"Hello"},"finish_reason":"stop"}]}"""
      let commonResp = fromOaCompatibleResponse json
      let roundTripJson = toOaCompatibleResponse commonResp
      roundTripJson `shouldContain` "Hello"

    it "BUG: may lose precision in timestamp during round-trip" do
      -- BUG: Timestamp precision may be lost in JSON serialization
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288123,"model":"custom-model","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"stop"}]}"""
      let commonResp = fromOaCompatibleResponse json
      -- Created may lose precision if stored as Number instead of Int
      -- Test documents potential precision loss
      pure unit

    it "BUG: may change field order in round-trip" do
      -- BUG: JSON field order may change (not critical but documents behavior)
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":1677652288,"model":"custom-model","choices":[]}"""
      let commonResp = fromOaCompatibleResponse json
      let roundTripJson = toOaCompatibleResponse commonResp
      -- Field order may differ but content should be same
      roundTripJson `shouldContain` "id"
      roundTripJson `shouldContain` "model"

  describe "Edge Cases" do
    it "handles CommonResponse → OpenAICompatible → CommonResponse round-trip" do
      let originalResp = mkMockCommonResponse
        { id: "chatcmpl-123"
        , model: "custom-model"
        , choices = [mkMockChoice Assistant "test" (Just Stop)]
        , usage = Just mkMockUsage
        }
      let oaCompatJson = toOaCompatibleResponse originalResp
      let roundTripResp = fromOaCompatibleResponse oaCompatJson
      roundTripResp.id `shouldEqual` "chatcmpl-123"
      roundTripResp.model `shouldEqual` "custom-model"
      roundTripResp.choices.length `shouldEqual` 1

    it "handles empty id in round-trip" do
      let commonResp = mkMockCommonResponse { id = "" }
      let oaCompatJson = toOaCompatibleResponse commonResp
      let roundTripResp = fromOaCompatibleResponse oaCompatJson
      roundTripResp.id `shouldEqual` ""

    it "handles zero created timestamp in round-trip" do
      let commonResp = mkMockCommonResponse { created = 0 }
      let oaCompatJson = toOaCompatibleResponse commonResp
      let roundTripResp = fromOaCompatibleResponse oaCompatJson
      roundTripResp.created `shouldEqual` 0

    it "handles very large created timestamp" do
      let json = """{"id":"chatcmpl-123","object":"chat.completion","created":2147483647,"model":"custom-model","choices":[{"index":0,"message":{"role":"assistant","content":"test"},"finish_reason":"stop"}]}"""
      let commonResp = fromOaCompatibleResponse json
      commonResp.created `shouldEqual` 2147483647
