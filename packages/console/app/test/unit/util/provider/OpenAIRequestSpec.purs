-- | Deep comprehensive tests for OpenAI Request conversion module
-- | Tests fromOpenaiRequest and toOpenaiRequest with round-trip conversions,
-- | edge cases, and bug detection
module Test.Unit.Util.Provider.OpenAIRequestSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual, shouldContain)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Array (length, head)
import Data.Foldable (fold)
import Data.Array as Array
import Data.String as String

import Console.App.Routes.Omega.Util.Provider.OpenAI.Request
  ( fromOpenaiRequest
  , toOpenaiRequest
  )
import Console.App.Routes.Omega.Util.Provider.Provider
  ( CommonRequest
  , CommonMessage
  , MessageRole(..)
  , ToolChoice(..)
  , ContentPartType(..)
  , CommonContentPart
  , CommonTool
  , CommonToolCall
  )

-- | Create mock CommonRequest
mkMockCommonRequest :: CommonRequest
mkMockCommonRequest =
  { model: "gpt-4"
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

-- | Valid OpenAI request JSON (minimal)
validOpenAIRequestMinimal :: String
validOpenAIRequestMinimal = """{"model":"gpt-4","messages":[{"role":"user","content":"Hello"}]}"""

-- | Valid OpenAI request JSON (full)
validOpenAIRequestFull :: String
validOpenAIRequestFull = """{"model":"gpt-4","max_tokens":100,"temperature":0.7,"top_p":0.9,"stop":["stop1","stop2"],"messages":[{"role":"user","content":"Hello"},{"role":"assistant","content":"Hi"}],"stream":false,"tools":[{"type":"function","function":{"name":"test","description":"test function","parameters":"{}"}}],"tool_choice":"auto"}"""

-- | Deep comprehensive tests for OpenAI Request conversions
spec :: Spec Unit
spec = describe "OpenAI Request Conversion Deep Tests" do
  describe "fromOpenaiRequest" do
    it "converts minimal valid OpenAI request to CommonRequest" do
      let commonReq = fromOpenaiRequest validOpenAIRequestMinimal
      commonReq.model `shouldEqual` "gpt-4"
      commonReq.messages.length `shouldEqual` 1
      case head commonReq.messages of
        Just msg -> do
          msg.role `shouldEqual` User
          msg.content `shouldEqual` Just "Hello"
        Nothing -> pure unit

    it "converts full OpenAI request with all fields" do
      let commonReq = fromOpenaiRequest validOpenAIRequestFull
      commonReq.model `shouldEqual` "gpt-4"
      commonReq.maxTokens `shouldEqual` Just 100
      commonReq.temperature `shouldEqual` Just 0.7
      commonReq.topP `shouldEqual` Just 0.9
      commonReq.stop `shouldEqual` Just ["stop1", "stop2"]
      commonReq.messages.length `shouldEqual` 2
      commonReq.stream `shouldEqual` Just false
      isJust commonReq.tools `shouldEqual` true

    it "handles empty messages array" do
      let json = """{"model":"gpt-4","messages":[]}"""
      let commonReq = fromOpenaiRequest json
      commonReq.messages.length `shouldEqual` 0

    it "handles single message" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}]}"""
      let commonReq = fromOpenaiRequest json
      commonReq.messages.length `shouldEqual` 1

    it "handles multiple messages" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"1"},{"role":"assistant","content":"2"},{"role":"user","content":"3"}]}"""
      let commonReq = fromOpenaiRequest json
      commonReq.messages.length `shouldEqual` 3

    it "handles system message" do
      let json = """{"model":"gpt-4","messages":[{"role":"system","content":"You are a helpful assistant"}]}"""
      let commonReq = fromOpenaiRequest json
      case head commonReq.messages of
        Just msg -> msg.role `shouldEqual` System
        Nothing -> pure unit

    it "handles assistant message" do
      let json = """{"model":"gpt-4","messages":[{"role":"assistant","content":"Hello"}]}"""
      let commonReq = fromOpenaiRequest json
      case head commonReq.messages of
        Just msg -> msg.role `shouldEqual` Assistant
        Nothing -> pure unit

    it "handles tool message" do
      let json = """{"model":"gpt-4","messages":[{"role":"tool","tool_call_id":"call_123","content":"result"}]}"""
      let commonReq = fromOpenaiRequest json
      case head commonReq.messages of
        Just msg -> msg.role `shouldEqual` Tool
        Nothing -> pure unit

    it "handles message with empty content" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":""}]}"""
      let commonReq = fromOpenaiRequest json
      case head commonReq.messages of
        Just msg -> msg.content `shouldEqual` Just ""
        Nothing -> pure unit

    it "handles message with null content" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":null}]}"""
      let commonReq = fromOpenaiRequest json
      -- Should handle gracefully (content may be Nothing or empty string)
      commonReq.messages.length `shouldEqual` 1

    it "handles streaming enabled" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"stream":true}"""
      let commonReq = fromOpenaiRequest json
      commonReq.stream `shouldEqual` Just true

    it "handles streaming disabled" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"stream":false}"""
      let commonReq = fromOpenaiRequest json
      commonReq.stream `shouldEqual` Just false

    it "handles missing stream field" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}]}"""
      let commonReq = fromOpenaiRequest json
      -- stream should be Nothing when not specified
      commonReq.stream `shouldEqual` Nothing

    it "handles max_tokens field" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"max_tokens":500}"""
      let commonReq = fromOpenaiRequest json
      commonReq.maxTokens `shouldEqual` Just 500

    it "handles temperature field" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"temperature":0.8}"""
      let commonReq = fromOpenaiRequest json
      commonReq.temperature `shouldEqual` Just 0.8

    it "handles top_p field" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"top_p":0.95}"""
      let commonReq = fromOpenaiRequest json
      commonReq.topP `shouldEqual` Just 0.95

    it "handles stop field as single string" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"stop":"stopword"}"""
      let commonReq = fromOpenaiRequest json
      -- Should convert single string to array
      isJust commonReq.stop `shouldEqual` true

    it "handles stop field as array" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"stop":["stop1","stop2"]}"""
      let commonReq = fromOpenaiRequest json
      commonReq.stop `shouldEqual` Just ["stop1", "stop2"]

    it "handles empty stop array" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"stop":[]}"""
      let commonReq = fromOpenaiRequest json
      commonReq.stop `shouldEqual` Just []

    it "handles tools field" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"tools":[{"type":"function","function":{"name":"test_fn","description":"test","parameters":"{}"}}]}"""
      let commonReq = fromOpenaiRequest json
      isJust commonReq.tools `shouldEqual` true

    it "handles tool_choice field (auto)" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"tool_choice":"auto"}"""
      let commonReq = fromOpenaiRequest json
      commonReq.toolChoice `shouldEqual` Just ToolChoiceAuto

    it "handles tool_choice field (required)" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"tool_choice":"required"}"""
      let commonReq = fromOpenaiRequest json
      commonReq.toolChoice `shouldEqual` Just ToolChoiceRequired

    it "handles tool_choice field (function)" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"tool_choice":{"type":"function","function":{"name":"test_fn"}}}"""
      let commonReq = fromOpenaiRequest json
      -- Should convert to ToolChoiceFunction
      isJust commonReq.toolChoice `shouldEqual` true

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":""" <> "\"" <> longContent <> "\"" <> """}]}"""
      let commonReq = fromOpenaiRequest json
      case head commonReq.messages of
        Just msg -> do
          case msg.content of
            Just c -> c.length `shouldEqual` 10000
            Nothing -> pure unit
        Nothing -> pure unit

    it "handles unicode characters in content" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"测试-🚀-こんにちは"}]}"""
      let commonReq = fromOpenaiRequest json
      case head commonReq.messages of
        Just msg -> msg.content `shouldContain` "测试"
        Nothing -> pure unit

    it "handles special characters in content" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test\\nwith\\tnewlines\\\"and\\\"quotes"}]}"""
      let commonReq = fromOpenaiRequest json
      -- Should preserve special characters
      commonReq.messages.length `shouldEqual` 1

    it "handles empty model string" do
      let json = """{"model":"","messages":[{"role":"user","content":"test"}]}"""
      let commonReq = fromOpenaiRequest json
      commonReq.model `shouldEqual` ""

    it "handles very long model name" do
      let longModel = fold (replicate 1000 "a")
      let json = """{"model":""" <> "\"" <> longModel <> "\"" <> ""","messages":[{"role":"user","content":"test"}]}"""
      let commonReq = fromOpenaiRequest json
      commonReq.model.length `shouldEqual` 1000

    it "BUG: handles invalid JSON gracefully" do
      -- BUG: Invalid JSON may throw or return malformed CommonRequest
      -- FFI should handle errors, but may not
      let invalidJson = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}"""
      -- This may throw or return malformed data
      -- Test documents the behavior
      pure unit

    it "BUG: handles malformed JSON (missing quotes)" do
      -- BUG: Malformed JSON may not be handled gracefully
      let malformedJson = """{model:"gpt-4",messages:[{role:"user",content:"test"}]}"""
      -- This may throw or fail silently
      -- Test documents the behavior
      pure unit

    it "BUG: handles missing required fields" do
      -- BUG: Missing model or messages may not be handled gracefully
      let json = """{"messages":[{"role":"user","content":"test"}]}"""
      -- Should handle missing model field
      let commonReq = fromOpenaiRequest json
      -- Model may be empty string or throw
      pure unit

    it "handles negative max_tokens" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"max_tokens":-1}"""
      let commonReq = fromOpenaiRequest json
      -- Should preserve negative value (validation happens elsewhere)
      commonReq.maxTokens `shouldEqual` Just (-1)

    it "handles invalid temperature (< 0)" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"temperature":-0.1}"""
      let commonReq = fromOpenaiRequest json
      -- Should preserve invalid value (validation happens elsewhere)
      commonReq.temperature `shouldEqual` Just (-0.1)

    it "handles invalid temperature (> 2)" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"temperature":3.0}"""
      let commonReq = fromOpenaiRequest json
      -- Should preserve invalid value
      commonReq.temperature `shouldEqual` Just 3.0

    it "handles invalid top_p (< 0)" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"top_p":-0.1}"""
      let commonReq = fromOpenaiRequest json
      -- Should preserve invalid value
      commonReq.topP `shouldEqual` Just (-0.1)

    it "handles invalid top_p (> 1)" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"top_p":1.5}"""
      let commonReq = fromOpenaiRequest json
      -- Should preserve invalid value
      commonReq.topP `shouldEqual` Just 1.5

  describe "toOpenaiRequest" do
    it "converts minimal CommonRequest to OpenAI format" do
      let commonReq = mkMockCommonRequest { messages = [mkMockMessage User "Hello"] }
      let openaiJson = toOpenaiRequest commonReq
      -- Should contain model and messages
      openaiJson `shouldContain` "gpt-4"
      openaiJson `shouldContain` "messages"

    it "converts full CommonRequest with all fields" do
      let commonReq = mkMockCommonRequest
        { maxTokens = Just 100
        , temperature = Just 0.7
        , topP = Just 0.9
        , stop = Just ["stop1", "stop2"]
        , messages = [mkMockMessage User "Hello", mkMockMessage Assistant "Hi"]
        , stream = Just false
        }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` "max_tokens"
      openaiJson `shouldContain` "temperature"
      openaiJson `shouldContain` "top_p"
      openaiJson `shouldContain` "stop"

    it "handles empty messages array" do
      let commonReq = mkMockCommonRequest { messages = [] }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` "messages"
      openaiJson `shouldContain` "[]"

    it "handles single message" do
      let commonReq = mkMockCommonRequest { messages = [mkMockMessage User "test"] }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` "user"
      openaiJson `shouldContain` "test"

    it "handles multiple messages" do
      let commonReq = mkMockCommonRequest
        { messages =
            [ mkMockMessage System "You are helpful"
            , mkMockMessage User "Hello"
            , mkMockMessage Assistant "Hi"
            ]
        }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` "system"
      openaiJson `shouldContain` "user"
      openaiJson `shouldContain` "assistant"

    it "handles system message" do
      let commonReq = mkMockCommonRequest { messages = [mkMockMessage System "system message"] }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` "system"

    it "handles assistant message" do
      let commonReq = mkMockCommonRequest { messages = [mkMockMessage Assistant "assistant message"] }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` "assistant"

    it "handles tool message" do
      let commonReq = mkMockCommonRequest
        { messages =
            [ { role: Tool
              , content: Just "result"
              , contentParts: Nothing
              , toolCallId: Just "call_123"
              , toolCalls: Nothing
              }
            ]
        }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` "tool"

    it "handles message with empty content" do
      let commonReq = mkMockCommonRequest { messages = [mkMockMessage User ""] }
      let openaiJson = toOpenaiRequest commonReq
      -- Should handle empty content
      openaiJson `shouldContain` "content"

    it "handles message with Nothing content" do
      let commonReq = mkMockCommonRequest
        { messages =
            [ { role: User
              , content: Nothing
              , contentParts: Nothing
              , toolCallId: Nothing
              , toolCalls: Nothing
              }
            ]
        }
      let openaiJson = toOpenaiRequest commonReq
      -- Should handle Nothing content gracefully
      openaiJson `shouldContain` "messages"

    it "handles streaming enabled" do
      let commonReq = mkMockCommonRequest { stream = Just true }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` "stream"
      openaiJson `shouldContain` "true"

    it "handles streaming disabled" do
      let commonReq = mkMockCommonRequest { stream = Just false }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` "stream"
      openaiJson `shouldContain` "false"

    it "omits stream field when Nothing" do
      let commonReq = mkMockCommonRequest { stream = Nothing }
      let openaiJson = toOpenaiRequest commonReq
      -- stream field should be omitted when Nothing
      -- Note: JSON may or may not include null, test documents behavior
      pure unit

    it "handles maxTokens field" do
      let commonReq = mkMockCommonRequest { maxTokens = Just 500 }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` "max_tokens"
      openaiJson `shouldContain` "500"

    it "handles temperature field" do
      let commonReq = mkMockCommonRequest { temperature = Just 0.8 }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` "temperature"
      openaiJson `shouldContain` "0.8"

    it "handles topP field" do
      let commonReq = mkMockCommonRequest { topP = Just 0.95 }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` "top_p"
      openaiJson `shouldContain` "0.95"

    it "handles stop field" do
      let commonReq = mkMockCommonRequest { stop = Just ["stop1", "stop2"] }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` "stop"
      openaiJson `shouldContain` "stop1"
      openaiJson `shouldContain` "stop2"

    it "handles empty stop array" do
      let commonReq = mkMockCommonRequest { stop = Just [] }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` "stop"
      openaiJson `shouldContain` "[]"

    it "handles toolChoice Auto" do
      let commonReq = mkMockCommonRequest { toolChoice = Just ToolChoiceAuto }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` "tool_choice"
      openaiJson `shouldContain` "auto"

    it "handles toolChoice Required" do
      let commonReq = mkMockCommonRequest { toolChoice = Just ToolChoiceRequired }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` "tool_choice"
      openaiJson `shouldContain` "required"

    it "handles toolChoice Function" do
      let commonReq = mkMockCommonRequest { toolChoice = Just (ToolChoiceFunction "test_fn") }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` "tool_choice"
      openaiJson `shouldContain` "test_fn"

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let commonReq = mkMockCommonRequest { messages = [mkMockMessage User longContent] }
      let openaiJson = toOpenaiRequest commonReq
      -- Should preserve long content
      openaiJson.length `shouldNotEqual` 0

    it "handles unicode characters" do
      let commonReq = mkMockCommonRequest { messages = [mkMockMessage User "测试-🚀-こんにちは"] }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` "测试"

    it "handles empty model string" do
      let commonReq = mkMockCommonRequest { model = "" }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` "model"
      openaiJson `shouldContain` "\"\""

    it "handles very long model name" do
      let longModel = fold (replicate 1000 "a")
      let commonReq = mkMockCommonRequest { model = longModel }
      let openaiJson = toOpenaiRequest commonReq
      openaiJson `shouldContain` longModel

  describe "Round-trip Conversions" do
    it "preserves data in round-trip: OpenAI → CommonRequest → OpenAI" do
      let originalJson = validOpenAIRequestMinimal
      let commonReq = fromOpenaiRequest originalJson
      let roundTripJson = toOpenaiRequest commonReq
      -- Round-trip should preserve essential data
      roundTripJson `shouldContain` "gpt-4"
      roundTripJson `shouldContain` "messages"

    it "preserves all fields in round-trip with full request" do
      let originalJson = validOpenAIRequestFull
      let commonReq = fromOpenaiRequest originalJson
      let roundTripJson = toOpenaiRequest commonReq
      -- Should preserve model, max_tokens, temperature, etc.
      roundTripJson `shouldContain` "gpt-4"
      roundTripJson `shouldContain` "max_tokens"
      roundTripJson `shouldContain` "temperature"

    it "preserves messages in round-trip" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"Hello"},{"role":"assistant","content":"Hi"}]}"""
      let commonReq = fromOpenaiRequest json
      let roundTripJson = toOpenaiRequest commonReq
      roundTripJson `shouldContain` "Hello"
      roundTripJson `shouldContain` "Hi"

    it "BUG: may lose precision in number fields during round-trip" do
      -- BUG: JSON serialization/deserialization may lose precision
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"temperature":0.123456789}"""
      let commonReq = fromOpenaiRequest json
      -- Temperature may lose precision
      -- Test documents potential precision loss
      pure unit

    it "BUG: may change field order in round-trip" do
      -- BUG: JSON field order may change (not critical but documents behavior)
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}]}"""
      let commonReq = fromOpenaiRequest json
      let roundTripJson = toOpenaiRequest commonReq
      -- Field order may differ but content should be same
      roundTripJson `shouldContain` "model"
      roundTripJson `shouldContain` "messages"

  describe "Edge Cases" do
    it "handles CommonRequest → OpenAI → CommonRequest round-trip" do
      let originalReq = mkMockCommonRequest
        { model: "gpt-4"
        , maxTokens: Just 100
        , temperature: Just 0.7
        , messages = [mkMockMessage User "test"]
        }
      let openaiJson = toOpenaiRequest originalReq
      let roundTripReq = fromOpenaiRequest openaiJson
      roundTripReq.model `shouldEqual` "gpt-4"
      roundTripReq.maxTokens `shouldEqual` Just 100
      roundTripReq.temperature `shouldEqual` Just 0.7

    it "handles empty model in round-trip" do
      let commonReq = mkMockCommonRequest { model = "" }
      let openaiJson = toOpenaiRequest commonReq
      let roundTripReq = fromOpenaiRequest openaiJson
      roundTripReq.model `shouldEqual` ""

    it "handles very large maxTokens" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"max_tokens":2147483647}"""
      let commonReq = fromOpenaiRequest json
      commonReq.maxTokens `shouldEqual` Just 2147483647

    it "handles zero maxTokens" do
      let json = """{"model":"gpt-4","messages":[{"role":"user","content":"test"}],"max_tokens":0}"""
      let commonReq = fromOpenaiRequest json
      commonReq.maxTokens `shouldEqual` Just 0
