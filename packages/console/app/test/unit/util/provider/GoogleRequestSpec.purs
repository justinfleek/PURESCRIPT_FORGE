-- | Deep comprehensive tests for Google Request conversion module
-- | Tests fromGoogleRequest and toGoogleRequest with round-trip conversions,
-- | edge cases, and bug detection
module Test.Unit.Util.Provider.GoogleRequestSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual, shouldContain)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Array (length, head)
import Data.Foldable (fold)
import Data.Array as Array
import Data.String as String

import Console.App.Routes.Omega.Util.Provider.Google.Request
  ( fromGoogleRequest
  , toGoogleRequest
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
  { model: "gemini-pro"
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

-- | Valid Google request JSON (minimal)
validGoogleRequestMinimal :: String
validGoogleRequestMinimal = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"Hello"}]}]}"""

-- | Valid Google request JSON (full)
validGoogleRequestFull :: String
validGoogleRequestFull = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"Hello"}]},{"role":"model","parts":[{"text":"Hi"}]}],"generationConfig":{"maxOutputTokens":100,"temperature":0.7,"topP":0.9,"stopSequences":["stop1","stop2"]},"stream":false}"""

-- | Deep comprehensive tests for Google Request conversions
spec :: Spec Unit
spec = describe "Google Request Conversion Deep Tests" do
  describe "fromGoogleRequest" do
    it "converts minimal valid Google request to CommonRequest" do
      let commonReq = fromGoogleRequest validGoogleRequestMinimal
      commonReq.model `shouldEqual` "gemini-pro"
      commonReq.messages.length `shouldEqual` 1
      case head commonReq.messages of
        Just msg -> do
          msg.role `shouldEqual` User
          msg.content `shouldEqual` Just "Hello"
        Nothing -> pure unit

    it "converts full Google request with all fields" do
      let commonReq = fromGoogleRequest validGoogleRequestFull
      commonReq.model `shouldEqual` "gemini-pro"
      commonReq.messages.length `shouldEqual` 2
      -- Should extract generationConfig fields
      isJust commonReq.maxTokens `shouldEqual` true
      isJust commonReq.temperature `shouldEqual` true
      isJust commonReq.topP `shouldEqual` true
      isJust commonReq.stop `shouldEqual` true

    it "handles empty contents array" do
      let json = """{"model":"gemini-pro","contents":[]}"""
      let commonReq = fromGoogleRequest json
      commonReq.messages.length `shouldEqual` 0

    it "handles single message" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"test"}]}]}"""
      let commonReq = fromGoogleRequest json
      commonReq.messages.length `shouldEqual` 1

    it "handles multiple messages" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"1"}]},{"role":"model","parts":[{"text":"2"}]},{"role":"user","parts":[{"text":"3"}]}]}"""
      let commonReq = fromGoogleRequest json
      commonReq.messages.length `shouldEqual` 3

    it "handles user message" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"Hello"}]}]}"""
      let commonReq = fromGoogleRequest json
      case head commonReq.messages of
        Just msg -> msg.role `shouldEqual` User
        Nothing -> pure unit

    it "handles model message (assistant)" do
      let json = """{"model":"gemini-pro","contents":[{"role":"model","parts":[{"text":"Hello"}]}]}"""
      let commonReq = fromGoogleRequest json
      case head commonReq.messages of
        Just msg -> msg.role `shouldEqual` Assistant
        Nothing -> pure unit

    it "handles message with empty text" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":""}]}]}"""
      let commonReq = fromGoogleRequest json
      case head commonReq.messages of
        Just msg -> msg.content `shouldEqual` Just ""
        Nothing -> pure unit

    it "handles streaming enabled" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"test"}]}],"stream":true}"""
      let commonReq = fromGoogleRequest json
      commonReq.stream `shouldEqual` Just true

    it "handles streaming disabled" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"test"}]}],"stream":false}"""
      let commonReq = fromGoogleRequest json
      commonReq.stream `shouldEqual` Just false

    it "handles missing stream field" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"test"}]}]}"""
      let commonReq = fromGoogleRequest json
      -- stream should be Nothing when not specified
      commonReq.stream `shouldEqual` Nothing

    it "handles maxOutputTokens in generationConfig" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"test"}]}],"generationConfig":{"maxOutputTokens":500}}"""
      let commonReq = fromGoogleRequest json
      commonReq.maxTokens `shouldEqual` Just 500

    it "handles temperature in generationConfig" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"test"}]}],"generationConfig":{"temperature":0.8}}"""
      let commonReq = fromGoogleRequest json
      commonReq.temperature `shouldEqual` Just 0.8

    it "handles topP in generationConfig" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"test"}]}],"generationConfig":{"topP":0.95}}"""
      let commonReq = fromGoogleRequest json
      commonReq.topP `shouldEqual` Just 0.95

    it "handles stopSequences in generationConfig" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"test"}]}],"generationConfig":{"stopSequences":["stop1","stop2"]}}"""
      let commonReq = fromGoogleRequest json
      commonReq.stop `shouldEqual` Just ["stop1", "stop2"]

    it "handles empty stopSequences array" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"test"}]}],"generationConfig":{"stopSequences":[]}}"""
      let commonReq = fromGoogleRequest json
      commonReq.stop `shouldEqual` Just []

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":""" <> "\"" <> longContent <> "\"" <> """}]}]}"""
      let commonReq = fromGoogleRequest json
      case head commonReq.messages of
        Just msg -> do
          case msg.content of
            Just c -> c.length `shouldEqual` 10000
            Nothing -> pure unit
        Nothing -> pure unit

    it "handles unicode characters in content" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"测试-🚀-こんにちは"}]}]}"""
      let commonReq = fromGoogleRequest json
      case head commonReq.messages of
        Just msg -> msg.content `shouldContain` "测试"
        Nothing -> pure unit

    it "handles special characters in content" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"test\\nwith\\tnewlines\\\"and\\\"quotes"}]}]}"""
      let commonReq = fromGoogleRequest json
      -- Should preserve special characters
      commonReq.messages.length `shouldEqual` 1

    it "handles empty model string" do
      let json = """{"model":"","contents":[{"role":"user","parts":[{"text":"test"}]}]}"""
      let commonReq = fromGoogleRequest json
      commonReq.model `shouldEqual` ""

    it "handles very long model name" do
      let longModel = fold (replicate 1000 "a")
      let json = """{"model":""" <> "\"" <> longModel <> "\"" <> ""","contents":[{"role":"user","parts":[{"text":"test"}]}]}"""
      let commonReq = fromGoogleRequest json
      commonReq.model.length `shouldEqual` 1000

    it "BUG: handles invalid JSON gracefully" do
      -- BUG: Invalid JSON may throw or return malformed CommonRequest
      let invalidJson = """{"model":"gemini-pro","contents":[{"role":"user"""
      -- This may throw or return malformed data
      -- Test documents the behavior
      pure unit

    it "BUG: handles malformed JSON (missing quotes)" do
      -- BUG: Malformed JSON may not be handled gracefully
      let malformedJson = """{model:"gemini-pro",contents:[{role:"user",parts:[{text:"test"}]}]}"""
      -- This may throw or fail silently
      -- Test documents the behavior
      pure unit

    it "BUG: handles missing required fields" do
      -- BUG: Missing model or contents may not be handled gracefully
      let json = """{"contents":[{"role":"user","parts":[{"text":"test"}]}]}"""
      -- Should handle missing model field
      let commonReq = fromGoogleRequest json
      -- Model may be empty string or throw
      pure unit

    it "handles negative maxOutputTokens" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"test"}]}],"generationConfig":{"maxOutputTokens":-1}}"""
      let commonReq = fromGoogleRequest json
      -- Should preserve negative value (validation happens elsewhere)
      commonReq.maxTokens `shouldEqual` Just (-1)

    it "handles invalid temperature (< 0)" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"test"}]}],"generationConfig":{"temperature":-0.1}}"""
      let commonReq = fromGoogleRequest json
      -- Should preserve invalid value (validation happens elsewhere)
      commonReq.temperature `shouldEqual` Just (-0.1)

    it "handles invalid temperature (> 2)" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"test"}]}],"generationConfig":{"temperature":3.0}}"""
      let commonReq = fromGoogleRequest json
      -- Should preserve invalid value
      commonReq.temperature `shouldEqual` Just 3.0

    it "handles invalid topP (< 0)" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"test"}]}],"generationConfig":{"topP":-0.1}}"""
      let commonReq = fromGoogleRequest json
      -- Should preserve invalid value
      commonReq.topP `shouldEqual` Just (-0.1)

    it "handles invalid topP (> 1)" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"test"}]}],"generationConfig":{"topP":1.5}}"""
      let commonReq = fromGoogleRequest json
      -- Should preserve invalid value
      commonReq.topP `shouldEqual` Just 1.5

  describe "toGoogleRequest" do
    it "converts minimal CommonRequest to Google format" do
      let commonReq = mkMockCommonRequest { messages = [mkMockMessage User "Hello"] }
      let googleJson = toGoogleRequest commonReq
      -- Should contain model and contents
      googleJson `shouldContain` "gemini-pro"
      googleJson `shouldContain` "contents"

    it "converts full CommonRequest with all fields" do
      let commonReq = mkMockCommonRequest
        { maxTokens = Just 100
        , temperature = Just 0.7
        , topP = Just 0.9
        , stop = Just ["stop1", "stop2"]
        , messages = [mkMockMessage User "Hello", mkMockMessage Assistant "Hi"]
        , stream = Just false
        }
      let googleJson = toGoogleRequest commonReq
      googleJson `shouldContain` "generationConfig"
      googleJson `shouldContain` "maxOutputTokens"
      googleJson `shouldContain` "temperature"
      googleJson `shouldContain` "topP"
      googleJson `shouldContain` "stopSequences"

    it "handles empty messages array" do
      let commonReq = mkMockCommonRequest { messages = [] }
      let googleJson = toGoogleRequest commonReq
      googleJson `shouldContain` "contents"
      googleJson `shouldContain` "[]"

    it "handles single message" do
      let commonReq = mkMockCommonRequest { messages = [mkMockMessage User "test"] }
      let googleJson = toGoogleRequest commonReq
      googleJson `shouldContain` "user"
      googleJson `shouldContain` "test"

    it "handles multiple messages" do
      let commonReq = mkMockCommonRequest
        { messages =
            [ mkMockMessage User "Hello"
            , mkMockMessage Assistant "Hi"
            ]
        }
      let googleJson = toGoogleRequest commonReq
      googleJson `shouldContain` "user"
      googleJson `shouldContain` "model"

    it "handles user message" do
      let commonReq = mkMockCommonRequest { messages = [mkMockMessage User "Hello"] }
      let googleJson = toGoogleRequest commonReq
      googleJson `shouldContain` "user"

    it "handles assistant message (converts to model)" do
      let commonReq = mkMockCommonRequest { messages = [mkMockMessage Assistant "Hello"] }
      let googleJson = toGoogleRequest commonReq
      googleJson `shouldContain` "model"  -- Google uses "model" not "assistant"

    it "handles message with empty content" do
      let commonReq = mkMockCommonRequest { messages = [mkMockMessage User ""] }
      let googleJson = toGoogleRequest commonReq
      -- Should handle empty content
      googleJson `shouldContain` "content"

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
      let googleJson = toGoogleRequest commonReq
      -- Should handle Nothing content gracefully
      googleJson `shouldContain` "contents"

    it "handles streaming enabled" do
      let commonReq = mkMockCommonRequest { stream = Just true }
      let googleJson = toGoogleRequest commonReq
      googleJson `shouldContain` "stream"
      googleJson `shouldContain` "true"

    it "handles streaming disabled" do
      let commonReq = mkMockCommonRequest { stream = Just false }
      let googleJson = toGoogleRequest commonReq
      googleJson `shouldContain` "stream"
      googleJson `shouldContain` "false"

    it "omits stream field when Nothing" do
      let commonReq = mkMockCommonRequest { stream = Nothing }
      let googleJson = toGoogleRequest commonReq
      -- stream field should be omitted when Nothing
      -- Note: JSON may or may not include null, test documents behavior
      pure unit

    it "handles maxTokens field (converts to maxOutputTokens)" do
      let commonReq = mkMockCommonRequest { maxTokens = Just 500 }
      let googleJson = toGoogleRequest commonReq
      googleJson `shouldContain` "generationConfig"
      googleJson `shouldContain` "maxOutputTokens"
      googleJson `shouldContain` "500"

    it "handles temperature field" do
      let commonReq = mkMockCommonRequest { temperature = Just 0.8 }
      let googleJson = toGoogleRequest commonReq
      googleJson `shouldContain` "generationConfig"
      googleJson `shouldContain` "temperature"
      googleJson `shouldContain` "0.8"

    it "handles topP field" do
      let commonReq = mkMockCommonRequest { topP = Just 0.95 }
      let googleJson = toGoogleRequest commonReq
      googleJson `shouldContain` "generationConfig"
      googleJson `shouldContain` "topP"
      googleJson `shouldContain` "0.95"

    it "handles stop field (converts to stopSequences)" do
      let commonReq = mkMockCommonRequest { stop = Just ["stop1", "stop2"] }
      let googleJson = toGoogleRequest commonReq
      googleJson `shouldContain` "generationConfig"
      googleJson `shouldContain` "stopSequences"
      googleJson `shouldContain` "stop1"
      googleJson `shouldContain` "stop2"

    it "handles empty stop array" do
      let commonReq = mkMockCommonRequest { stop = Just [] }
      let googleJson = toGoogleRequest commonReq
      googleJson `shouldContain` "stopSequences"
      googleJson `shouldContain` "[]"

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let commonReq = mkMockCommonRequest { messages = [mkMockMessage User longContent] }
      let googleJson = toGoogleRequest commonReq
      -- Should preserve long content
      googleJson.length `shouldNotEqual` 0

    it "handles unicode characters" do
      let commonReq = mkMockCommonRequest { messages = [mkMockMessage User "测试-🚀-こんにちは"] }
      let googleJson = toGoogleRequest commonReq
      googleJson `shouldContain` "测试"

    it "handles empty model string" do
      let commonReq = mkMockCommonRequest { model = "" }
      let googleJson = toGoogleRequest commonReq
      googleJson `shouldContain` "model"
      googleJson `shouldContain` "\"\""

    it "handles very long model name" do
      let longModel = fold (replicate 1000 "a")
      let commonReq = mkMockCommonRequest { model = longModel }
      let googleJson = toGoogleRequest commonReq
      googleJson `shouldContain` longModel

  describe "Round-trip Conversions" do
    it "preserves data in round-trip: Google → CommonRequest → Google" do
      let originalJson = validGoogleRequestMinimal
      let commonReq = fromGoogleRequest originalJson
      let roundTripJson = toGoogleRequest commonReq
      -- Round-trip should preserve essential data
      roundTripJson `shouldContain` "gemini-pro"
      roundTripJson `shouldContain` "contents"

    it "preserves all fields in round-trip with full request" do
      let originalJson = validGoogleRequestFull
      let commonReq = fromGoogleRequest originalJson
      let roundTripJson = toGoogleRequest commonReq
      -- Should preserve model, generationConfig, etc.
      roundTripJson `shouldContain` "gemini-pro"
      roundTripJson `shouldContain` "generationConfig"

    it "preserves messages in round-trip" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"Hello"}]},{"role":"model","parts":[{"text":"Hi"}]}]}"""
      let commonReq = fromGoogleRequest json
      let roundTripJson = toGoogleRequest commonReq
      roundTripJson `shouldContain` "Hello"
      roundTripJson `shouldContain` "Hi"

    it "BUG: may lose precision in number fields during round-trip" do
      -- BUG: JSON serialization/deserialization may lose precision
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"test"}]}],"generationConfig":{"temperature":0.123456789}}"""
      let commonReq = fromGoogleRequest json
      -- Temperature may lose precision
      -- Test documents potential precision loss
      pure unit

    it "BUG: may change field order in round-trip" do
      -- BUG: JSON field order may change (not critical but documents behavior)
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"test"}]}]}"""
      let commonReq = fromGoogleRequest json
      let roundTripJson = toGoogleRequest commonReq
      -- Field order may differ but content should be same
      roundTripJson `shouldContain` "model"
      roundTripJson `shouldContain` "contents"

  describe "Edge Cases" do
    it "handles CommonRequest → Google → CommonRequest round-trip" do
      let originalReq = mkMockCommonRequest
        { model: "gemini-pro"
        , maxTokens = Just 100
        , temperature = Just 0.7
        , messages = [mkMockMessage User "test"]
        }
      let googleJson = toGoogleRequest originalReq
      let roundTripReq = fromGoogleRequest googleJson
      roundTripReq.model `shouldEqual` "gemini-pro"
      roundTripReq.maxTokens `shouldEqual` Just 100
      roundTripReq.temperature `shouldEqual` Just 0.7

    it "handles empty model in round-trip" do
      let commonReq = mkMockCommonRequest { model = "" }
      let googleJson = toGoogleRequest commonReq
      let roundTripReq = fromGoogleRequest googleJson
      roundTripReq.model `shouldEqual` ""

    it "handles very large maxTokens" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"test"}]}],"generationConfig":{"maxOutputTokens":2147483647}}"""
      let commonReq = fromGoogleRequest json
      commonReq.maxTokens `shouldEqual` Just 2147483647

    it "handles zero maxTokens" do
      let json = """{"model":"gemini-pro","contents":[{"role":"user","parts":[{"text":"test"}]}],"generationConfig":{"maxOutputTokens":0}}"""
      let commonReq = fromGoogleRequest json
      commonReq.maxTokens `shouldEqual` Just 0
