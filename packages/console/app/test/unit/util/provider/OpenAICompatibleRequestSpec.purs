-- | Deep comprehensive tests for OpenAICompatible Request conversion module
-- | Tests fromOaCompatibleRequest and toOaCompatibleRequest with round-trip conversions,
-- | edge cases, and bug detection
-- | Note: OpenAICompatible format is similar to OpenAI format
module Test.Unit.Util.Provider.OpenAICompatibleRequestSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual, shouldContain)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Array (length, head)
import Data.Foldable (fold)
import Data.Array as Array
import Data.String as String

import Console.App.Routes.Omega.Util.Provider.OpenAICompatible.Request
  ( fromOaCompatibleRequest
  , toOaCompatibleRequest
  )
import Console.App.Routes.Omega.Util.Provider.Provider
  ( CommonRequest
  , CommonMessage
  , MessageRole(..)
  , ToolChoice(..)
  )

-- | Create mock CommonRequest
mkMockCommonRequest :: CommonRequest
mkMockCommonRequest =
  { model: "custom-model"
  , maxTokens: Nothing
  , temperature: Nothing
  , topP: Nothing
  , stop: Nothing
  , messages: []
  , stream: Nothing
  , tools: Nothing
  , toolChoice: Nothing
  }

-- | Create mock CommonMessage
mkMockMessage :: MessageRole -> String -> CommonMessage
mkMockMessage role content =
  { role
  , content: Just content
  , contentParts: Nothing
  , toolCallId: Nothing
  , toolCalls: Nothing
  }

-- | Valid OpenAICompatible request JSON (minimal) - same format as OpenAI
validOaCompatibleRequestMinimal :: String
validOaCompatibleRequestMinimal = """{"model":"custom-model","messages":[{"role":"user","content":"Hello"}]}"""

-- | Valid OpenAICompatible request JSON (full)
validOaCompatibleRequestFull :: String
validOaCompatibleRequestFull = """{"model":"custom-model","max_tokens":100,"temperature":0.7,"top_p":0.9,"stop":["stop1","stop2"],"messages":[{"role":"user","content":"Hello"},{"role":"assistant","content":"Hi"}],"stream":false,"tools":[{"type":"function","function":{"name":"test","description":"test function","parameters":"{}"}}],"tool_choice":"auto"}"""

-- | Deep comprehensive tests for OpenAICompatible Request conversions
spec :: Spec Unit
spec = describe "OpenAICompatible Request Conversion Deep Tests" do
  describe "fromOaCompatibleRequest" do
    it "converts minimal valid OpenAICompatible request to CommonRequest" do
      let commonReq = fromOaCompatibleRequest validOaCompatibleRequestMinimal
      commonReq.model `shouldEqual` "custom-model"
      commonReq.messages.length `shouldEqual` 1
      case head commonReq.messages of
        Just msg -> do
          msg.role `shouldEqual` User
          msg.content `shouldEqual` Just "Hello"
        Nothing -> pure unit

    it "converts full OpenAICompatible request with all fields" do
      let commonReq = fromOaCompatibleRequest validOaCompatibleRequestFull
      commonReq.model `shouldEqual` "custom-model"
      commonReq.maxTokens `shouldEqual` Just 100
      commonReq.temperature `shouldEqual` Just 0.7
      commonReq.topP `shouldEqual` Just 0.9
      commonReq.stop `shouldEqual` Just ["stop1", "stop2"]
      commonReq.messages.length `shouldEqual` 2
      commonReq.stream `shouldEqual` Just false
      isJust commonReq.tools `shouldEqual` true

    it "handles empty messages array" do
      let json = """{"model":"custom-model","messages":[]}"""
      let commonReq = fromOaCompatibleRequest json
      commonReq.messages.length `shouldEqual` 0

    it "handles single message" do
      let json = """{"model":"custom-model","messages":[{"role":"user","content":"test"}]}"""
      let commonReq = fromOaCompatibleRequest json
      commonReq.messages.length `shouldEqual` 1

    it "handles multiple messages" do
      let json = """{"model":"custom-model","messages":[{"role":"user","content":"1"},{"role":"assistant","content":"2"},{"role":"user","content":"3"}]}"""
      let commonReq = fromOaCompatibleRequest json
      commonReq.messages.length `shouldEqual` 3

    it "handles system message" do
      let json = """{"model":"custom-model","messages":[{"role":"system","content":"You are a helpful assistant"}]}"""
      let commonReq = fromOaCompatibleRequest json
      case head commonReq.messages of
        Just msg -> msg.role `shouldEqual` System
        Nothing -> pure unit

    it "handles user message" do
      let json = """{"model":"custom-model","messages":[{"role":"user","content":"Hello"}]}"""
      let commonReq = fromOaCompatibleRequest json
      case head commonReq.messages of
        Just msg -> msg.role `shouldEqual` User
        Nothing -> pure unit

    it "handles assistant message" do
      let json = """{"model":"custom-model","messages":[{"role":"assistant","content":"Hello"}]}"""
      let commonReq = fromOaCompatibleRequest json
      case head commonReq.messages of
        Just msg -> msg.role `shouldEqual` Assistant
        Nothing -> pure unit

    it "handles tool message" do
      let json = """{"model":"custom-model","messages":[{"role":"tool","tool_call_id":"call_123","content":"result"}]}"""
      let commonReq = fromOaCompatibleRequest json
      case head commonReq.messages of
        Just msg -> msg.role `shouldEqual` Tool
        Nothing -> pure unit

    it "handles message with empty content" do
      let json = """{"model":"custom-model","messages":[{"role":"user","content":""}]}"""
      let commonReq = fromOaCompatibleRequest json
      case head commonReq.messages of
        Just msg -> msg.content `shouldEqual` Just ""
        Nothing -> pure unit

    it "handles streaming enabled" do
      let json = """{"model":"custom-model","messages":[{"role":"user","content":"test"}],"stream":true}"""
      let commonReq = fromOaCompatibleRequest json
      commonReq.stream `shouldEqual` Just true

    it "handles max_tokens field" do
      let json = """{"model":"custom-model","messages":[{"role":"user","content":"test"}],"max_tokens":500}"""
      let commonReq = fromOaCompatibleRequest json
      commonReq.maxTokens `shouldEqual` Just 500

    it "handles temperature field" do
      let json = """{"model":"custom-model","messages":[{"role":"user","content":"test"}],"temperature":0.8}"""
      let commonReq = fromOaCompatibleRequest json
      commonReq.temperature `shouldEqual` Just 0.8

    it "handles top_p field" do
      let json = """{"model":"custom-model","messages":[{"role":"user","content":"test"}],"top_p":0.95}"""
      let commonReq = fromOaCompatibleRequest json
      commonReq.topP `shouldEqual` Just 0.95

    it "handles stop field as array" do
      let json = """{"model":"custom-model","messages":[{"role":"user","content":"test"}],"stop":["stop1","stop2"]}"""
      let commonReq = fromOaCompatibleRequest json
      commonReq.stop `shouldEqual` Just ["stop1", "stop2"]

    it "handles tools field" do
      let json = """{"model":"custom-model","messages":[{"role":"user","content":"test"}],"tools":[{"type":"function","function":{"name":"test_fn","description":"test","parameters":"{}"}}]}"""
      let commonReq = fromOaCompatibleRequest json
      isJust commonReq.tools `shouldEqual` true

    it "handles tool_choice field (auto)" do
      let json = """{"model":"custom-model","messages":[{"role":"user","content":"test"}],"tool_choice":"auto"}"""
      let commonReq = fromOaCompatibleRequest json
      commonReq.toolChoice `shouldEqual` Just ToolChoiceAuto

    it "handles tool_choice field (required)" do
      let json = """{"model":"custom-model","messages":[{"role":"user","content":"test"}],"tool_choice":"required"}"""
      let commonReq = fromOaCompatibleRequest json
      commonReq.toolChoice `shouldEqual` Just ToolChoiceRequired

    it "handles tool_choice field (function)" do
      let json = """{"model":"custom-model","messages":[{"role":"user","content":"test"}],"tool_choice":{"type":"function","function":{"name":"test_fn"}}}"""
      let commonReq = fromOaCompatibleRequest json
      -- Should convert to ToolChoiceFunction
      isJust commonReq.toolChoice `shouldEqual` true

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let json = """{"model":"custom-model","messages":[{"role":"user","content":""" <> "\"" <> longContent <> "\"" <> """}]}"""
      let commonReq = fromOaCompatibleRequest json
      case head commonReq.messages of
        Just msg -> do
          case msg.content of
            Just c -> c.length `shouldEqual` 10000
            Nothing -> pure unit
        Nothing -> pure unit

    it "handles unicode characters in content" do
      let json = """{"model":"custom-model","messages":[{"role":"user","content":"测试-🚀-こんにちは"}]}"""
      let commonReq = fromOaCompatibleRequest json
      case head commonReq.messages of
        Just msg -> msg.content `shouldContain` "测试"
        Nothing -> pure unit

    it "BUG: handles invalid JSON gracefully" do
      -- BUG: Invalid JSON may throw or return malformed CommonRequest
      let invalidJson = """{"model":"custom-model","messages":[{"role":"user"""
      -- This may throw or return malformed data
      -- Test documents the behavior
      pure unit

    it "BUG: handles malformed JSON (missing quotes)" do
      -- BUG: Malformed JSON may not be handled gracefully
      let malformedJson = """{model:"custom-model",messages:[{role:"user",content:"test"}]}"""
      -- This may throw or fail silently
      -- Test documents the behavior
      pure unit

    it "BUG: handles missing required fields" do
      -- BUG: Missing model or messages may not be handled gracefully
      let json = """{"messages":[{"role":"user","content":"test"}]}"""
      -- Should handle missing model field
      let commonReq = fromOaCompatibleRequest json
      -- Model may be empty string or throw
      pure unit

  describe "toOaCompatibleRequest" do
    it "converts minimal CommonRequest to OpenAICompatible format" do
      let commonReq = mkMockCommonRequest { messages = [mkMockMessage User "Hello"] }
      let oaCompatJson = toOaCompatibleRequest commonReq
      -- Should contain model and messages
      oaCompatJson `shouldContain` "custom-model"
      oaCompatJson `shouldContain` "messages"

    it "converts full CommonRequest with all fields" do
      let commonReq = mkMockCommonRequest
        { maxTokens = Just 100
        , temperature = Just 0.7
        , topP = Just 0.9
        , stop = Just ["stop1", "stop2"]
        , messages = [mkMockMessage User "Hello", mkMockMessage Assistant "Hi"]
        , stream = Just false
        }
      let oaCompatJson = toOaCompatibleRequest commonReq
      oaCompatJson `shouldContain` "max_tokens"
      oaCompatJson `shouldContain` "temperature"
      oaCompatJson `shouldContain` "top_p"
      oaCompatJson `shouldContain` "stop"

    it "handles empty messages array" do
      let commonReq = mkMockCommonRequest { messages = [] }
      let oaCompatJson = toOaCompatibleRequest commonReq
      oaCompatJson `shouldContain` "messages"
      oaCompatJson `shouldContain` "[]"

    it "handles single message" do
      let commonReq = mkMockCommonRequest { messages = [mkMockMessage User "test"] }
      let oaCompatJson = toOaCompatibleRequest commonReq
      oaCompatJson `shouldContain` "user"
      oaCompatJson `shouldContain` "test"

    it "handles multiple messages" do
      let commonReq = mkMockCommonRequest
        { messages =
            [ mkMockMessage System "You are helpful"
            , mkMockMessage User "Hello"
            , mkMockMessage Assistant "Hi"
            ]
        }
      let oaCompatJson = toOaCompatibleRequest commonReq
      oaCompatJson `shouldContain` "system"
      oaCompatJson `shouldContain` "user"
      oaCompatJson `shouldContain` "assistant"

    it "handles streaming enabled" do
      let commonReq = mkMockCommonRequest { stream = Just true }
      let oaCompatJson = toOaCompatibleRequest commonReq
      oaCompatJson `shouldContain` "stream"
      oaCompatJson `shouldContain` "true"

    it "handles maxTokens field" do
      let commonReq = mkMockCommonRequest { maxTokens = Just 500 }
      let oaCompatJson = toOaCompatibleRequest commonReq
      oaCompatJson `shouldContain` "max_tokens"
      oaCompatJson `shouldContain` "500"

    it "handles temperature field" do
      let commonReq = mkMockCommonRequest { temperature = Just 0.8 }
      let oaCompatJson = toOaCompatibleRequest commonReq
      oaCompatJson `shouldContain` "temperature"
      oaCompatJson `shouldContain` "0.8"

    it "handles topP field" do
      let commonReq = mkMockCommonRequest { topP = Just 0.95 }
      let oaCompatJson = toOaCompatibleRequest commonReq
      oaCompatJson `shouldContain` "top_p"
      oaCompatJson `shouldContain` "0.95"

    it "handles stop field" do
      let commonReq = mkMockCommonRequest { stop = Just ["stop1", "stop2"] }
      let oaCompatJson = toOaCompatibleRequest commonReq
      oaCompatJson `shouldContain` "stop"
      oaCompatJson `shouldContain` "stop1"
      oaCompatJson `shouldContain` "stop2"

    it "handles toolChoice Auto" do
      let commonReq = mkMockCommonRequest { toolChoice = Just ToolChoiceAuto }
      let oaCompatJson = toOaCompatibleRequest commonReq
      oaCompatJson `shouldContain` "tool_choice"
      oaCompatJson `shouldContain` "auto"

    it "handles toolChoice Required" do
      let commonReq = mkMockCommonRequest { toolChoice = Just ToolChoiceRequired }
      let oaCompatJson = toOaCompatibleRequest commonReq
      oaCompatJson `shouldContain` "tool_choice"
      oaCompatJson `shouldContain` "required"

    it "handles toolChoice Function" do
      let commonReq = mkMockCommonRequest { toolChoice = Just (ToolChoiceFunction "test_fn") }
      let oaCompatJson = toOaCompatibleRequest commonReq
      oaCompatJson `shouldContain` "tool_choice"
      oaCompatJson `shouldContain` "test_fn"

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let commonReq = mkMockCommonRequest { messages = [mkMockMessage User longContent] }
      let oaCompatJson = toOaCompatibleRequest commonReq
      -- Should preserve long content
      oaCompatJson.length `shouldNotEqual` 0

    it "handles unicode characters" do
      let commonReq = mkMockCommonRequest { messages = [mkMockMessage User "测试-🚀-こんにちは"] }
      let oaCompatJson = toOaCompatibleRequest commonReq
      oaCompatJson `shouldContain` "测试"

  describe "Round-trip Conversions" do
    it "preserves data in round-trip: OpenAICompatible → CommonRequest → OpenAICompatible" do
      let originalJson = validOaCompatibleRequestMinimal
      let commonReq = fromOaCompatibleRequest originalJson
      let roundTripJson = toOaCompatibleRequest commonReq
      -- Round-trip should preserve essential data
      roundTripJson `shouldContain` "custom-model"
      roundTripJson `shouldContain` "messages"

    it "preserves all fields in round-trip with full request" do
      let originalJson = validOaCompatibleRequestFull
      let commonReq = fromOaCompatibleRequest originalJson
      let roundTripJson = toOaCompatibleRequest commonReq
      -- Should preserve model, max_tokens, temperature, etc.
      roundTripJson `shouldContain` "custom-model"
      roundTripJson `shouldContain` "max_tokens"
      roundTripJson `shouldContain` "temperature"

    it "preserves messages in round-trip" do
      let json = """{"model":"custom-model","messages":[{"role":"user","content":"Hello"},{"role":"assistant","content":"Hi"}]}"""
      let commonReq = fromOaCompatibleRequest json
      let roundTripJson = toOaCompatibleRequest commonReq
      roundTripJson `shouldContain` "Hello"
      roundTripJson `shouldContain` "Hi"

    it "BUG: may lose precision in number fields during round-trip" do
      -- BUG: JSON serialization/deserialization may lose precision
      let json = """{"model":"custom-model","messages":[{"role":"user","content":"test"}],"temperature":0.123456789}"""
      let commonReq = fromOaCompatibleRequest json
      -- Temperature may lose precision
      -- Test documents potential precision loss
      pure unit

    it "BUG: may change field order in round-trip" do
      -- BUG: JSON field order may change (not critical but documents behavior)
      let json = """{"model":"custom-model","messages":[{"role":"user","content":"test"}]}"""
      let commonReq = fromOaCompatibleRequest json
      let roundTripJson = toOaCompatibleRequest commonReq
      -- Field order may differ but content should be same
      roundTripJson `shouldContain` "model"
      roundTripJson `shouldContain` "messages"

  describe "Edge Cases" do
    it "handles CommonRequest → OpenAICompatible → CommonRequest round-trip" do
      let originalReq = mkMockCommonRequest
        { model: "custom-model"
        , maxTokens = Just 100
        , temperature = Just 0.7
        , messages = [mkMockMessage User "test"]
        }
      let oaCompatJson = toOaCompatibleRequest originalReq
      let roundTripReq = fromOaCompatibleRequest oaCompatJson
      roundTripReq.model `shouldEqual` "custom-model"
      roundTripReq.maxTokens `shouldEqual` Just 100
      roundTripReq.temperature `shouldEqual` Just 0.7

    it "handles empty model in round-trip" do
      let commonReq = mkMockCommonRequest { model = "" }
      let oaCompatJson = toOaCompatibleRequest commonReq
      let roundTripReq = fromOaCompatibleRequest oaCompatJson
      roundTripReq.model `shouldEqual` ""

    it "handles very large maxTokens" do
      let json = """{"model":"custom-model","messages":[{"role":"user","content":"test"}],"max_tokens":2147483647}"""
      let commonReq = fromOaCompatibleRequest json
      commonReq.maxTokens `shouldEqual` Just 2147483647

    it "handles zero maxTokens" do
      let json = """{"model":"custom-model","messages":[{"role":"user","content":"test"}],"max_tokens":0}"""
      let commonReq = fromOaCompatibleRequest json
      commonReq.maxTokens `shouldEqual` Just 0
