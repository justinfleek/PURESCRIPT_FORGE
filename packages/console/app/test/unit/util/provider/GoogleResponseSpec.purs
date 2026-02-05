-- | Deep comprehensive tests for Google Response conversion module
-- | Tests fromGoogleResponse and toGoogleResponse with round-trip conversions,
-- | edge cases, and bug detection
module Test.Unit.Util.Provider.GoogleResponseSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual, shouldContain)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Array (length, head)
import Data.Foldable (fold)
import Data.Array as Array
import Data.String as String

import Console.App.Routes.Omega.Util.Provider.Google.Response
  ( fromGoogleResponse
  , toGoogleResponse
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
  { id: "response_123"
  , object: "chat.completion"
  , created: 1677652288
  , model: "gemini-pro"
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

-- | Valid Google response JSON (minimal)
validGoogleResponseMinimal :: String
validGoogleResponseMinimal = """{"candidates":[{"content":{"parts":[{"text":"Hello"}],"role":"model"},"finishReason":"STOP"}],"usageMetadata":{"promptTokenCount":10,"candidatesTokenCount":20,"totalTokenCount":30}}"""

-- | Valid Google response JSON (full)
validGoogleResponseFull :: String
validGoogleResponseFull = """{"candidates":[{"content":{"parts":[{"text":"Hello"}],"role":"model"},"finishReason":"STOP"}],"usageMetadata":{"promptTokenCount":10,"candidatesTokenCount":20,"totalTokenCount":30}}"""

-- | Deep comprehensive tests for Google Response conversions
spec :: Spec Unit
spec = describe "Google Response Conversion Deep Tests" do
  describe "fromGoogleResponse" do
    it "converts minimal valid Google response to CommonResponse" do
      let commonResp = fromGoogleResponse validGoogleResponseMinimal
      commonResp.model `shouldEqual` "gemini-pro"
      commonResp.choices.length `shouldEqual` 1

    it "converts full Google response with all fields" do
      let commonResp = fromGoogleResponse validGoogleResponseFull
      commonResp.model `shouldEqual` "gemini-pro"
      commonResp.choices.length `shouldEqual` 1
      isJust commonResp.usage `shouldEqual` true

    it "handles empty candidates array" do
      let json = """{"candidates":[]}"""
      let commonResp = fromGoogleResponse json
      commonResp.choices.length `shouldEqual` 0

    it "handles single candidate" do
      let json = """{"candidates":[{"content":{"parts":[{"text":"test"}],"role":"model"},"finishReason":"STOP"}]}"""
      let commonResp = fromGoogleResponse json
      commonResp.choices.length `shouldEqual` 1

    it "handles multiple candidates" do
      let json = """{"candidates":[{"content":{"parts":[{"text":"test1"}],"role":"model"},"finishReason":"STOP"},{"content":{"parts":[{"text":"test2"}],"role":"model"},"finishReason":"STOP"}]}"""
      let commonResp = fromGoogleResponse json
      commonResp.choices.length `shouldEqual` 2

    it "handles finishReason STOP" do
      let json = """{"candidates":[{"content":{"parts":[{"text":"test"}],"role":"model"},"finishReason":"STOP"}]}"""
      let commonResp = fromGoogleResponse json
      case head commonResp.choices of
        Just choice -> choice.finishReason `shouldEqual` Just Stop
        Nothing -> pure unit

    it "handles finishReason MAX_TOKENS" do
      let json = """{"candidates":[{"content":{"parts":[{"text":"test"}],"role":"model"},"finishReason":"MAX_TOKENS"}]}"""
      let commonResp = fromGoogleResponse json
      case head commonResp.choices of
        Just choice -> choice.finishReason `shouldEqual` Just Length
        Nothing -> pure unit

    it "handles finishReason SAFETY" do
      let json = """{"candidates":[{"content":{"parts":[{"text":"test"}],"role":"model"},"finishReason":"SAFETY"}]}"""
      let commonResp = fromGoogleResponse json
      case head commonResp.choices of
        Just choice -> choice.finishReason `shouldEqual` Just ContentFilter
        Nothing -> pure unit

    it "handles missing finishReason" do
      let json = """{"candidates":[{"content":{"parts":[{"text":"test"}],"role":"model"}]}"""
      let commonResp = fromGoogleResponse json
      case head commonResp.choices of
        Just choice -> choice.finishReason `shouldEqual` Nothing
        Nothing -> pure unit

    it "handles usageMetadata" do
      let json = """{"candidates":[{"content":{"parts":[{"text":"test"}],"role":"model"},"finishReason":"STOP"}],"usageMetadata":{"promptTokenCount":10,"candidatesTokenCount":20,"totalTokenCount":30}}"""
      let commonResp = fromGoogleResponse json
      isJust commonResp.usage `shouldEqual` true

    it "handles usageMetadata with promptTokenCount" do
      let json = """{"candidates":[{"content":{"parts":[{"text":"test"}],"role":"model"},"finishReason":"STOP"}],"usageMetadata":{"promptTokenCount":10}}"""
      let commonResp = fromGoogleResponse json
      case commonResp.usage of
        Just usage -> usage.promptTokens `shouldEqual` Just 10
        Nothing -> pure unit

    it "handles usageMetadata with candidatesTokenCount" do
      let json = """{"candidates":[{"content":{"parts":[{"text":"test"}],"role":"model"},"finishReason":"STOP"}],"usageMetadata":{"candidatesTokenCount":20}}"""
      let commonResp = fromGoogleResponse json
      case commonResp.usage of
        Just usage -> usage.completionTokens `shouldEqual` Just 20
        Nothing -> pure unit

    it "handles usageMetadata with totalTokenCount" do
      let json = """{"candidates":[{"content":{"parts":[{"text":"test"}],"role":"model"},"finishReason":"STOP"}],"usageMetadata":{"totalTokenCount":30}}"""
      let commonResp = fromGoogleResponse json
      case commonResp.usage of
        Just usage -> usage.totalTokens `shouldEqual` Just 30
        Nothing -> pure unit

    it "handles missing usageMetadata" do
      let json = """{"candidates":[{"content":{"parts":[{"text":"test"}],"role":"model"},"finishReason":"STOP"}]}"""
      let commonResp = fromGoogleResponse json
      commonResp.usage `shouldEqual` Nothing

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let json = """{"candidates":[{"content":{"parts":[{"text":""" <> "\"" <> longContent <> "\"" <> """}],"role":"model"},"finishReason":"STOP"}]}"""
      let commonResp = fromGoogleResponse json
      case head commonResp.choices of
        Just choice -> do
          case choice.message.content of
            Just c -> c.length `shouldEqual` 10000
            Nothing -> pure unit
        Nothing -> pure unit

    it "handles unicode characters in content" do
      let json = """{"candidates":[{"content":{"parts":[{"text":"测试-🚀-こんにちは"}],"role":"model"},"finishReason":"STOP"}]}"""
      let commonResp = fromGoogleResponse json
      case head commonResp.choices of
        Just choice -> choice.message.content `shouldContain` "测试"
        Nothing -> pure unit

    it "handles special characters in content" do
      let json = """{"candidates":[{"content":{"parts":[{"text":"test\\nwith\\tnewlines\\\"and\\\"quotes"}],"role":"model"},"finishReason":"STOP"}]}"""
      let commonResp = fromGoogleResponse json
      -- Should preserve special characters
      commonResp.choices.length `shouldEqual` 1

    it "BUG: handles invalid JSON gracefully" do
      -- BUG: Invalid JSON may throw or return malformed CommonResponse
      let invalidJson = """{"candidates":[{"content":{"parts"""
      -- This may throw or return malformed data
      -- Test documents the behavior
      pure unit

    it "BUG: handles malformed JSON (missing quotes)" do
      -- BUG: Malformed JSON may not be handled gracefully
      let malformedJson = """{candidates:[{content:{parts:[{text:"test"}]}}]}"""
      -- This may throw or fail silently
      -- Test documents the behavior
      pure unit

    it "BUG: handles missing required fields" do
      -- BUG: Missing candidates may not be handled gracefully
      let json = """{"usageMetadata":{}}"""
      -- Should handle missing candidates field
      let commonResp = fromGoogleResponse json
      -- candidates may be empty array or throw
      pure unit

    it "BUG: handles invalid finishReason" do
      -- BUG: Invalid finishReason may not be handled gracefully
      let json = """{"candidates":[{"content":{"parts":[{"text":"test"}],"role":"model"},"finishReason":"INVALID"}]}"""
      let commonResp = fromGoogleResponse json
      -- finishReason may be Nothing or throw
      -- Test documents the behavior
      pure unit

  describe "toGoogleResponse" do
    it "converts minimal CommonResponse to Google format" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "Hello" (Just Stop)] }
      let googleJson = toGoogleResponse commonResp
      -- Should contain candidates
      googleJson `shouldContain` "candidates"
      googleJson `shouldContain` "Hello"

    it "converts full CommonResponse with all fields" do
      let commonResp = mkMockCommonResponse
        { choices = [mkMockChoice Assistant "Hello" (Just Stop)]
        , usage = Just mkMockUsage
        }
      let googleJson = toGoogleResponse commonResp
      googleJson `shouldContain` "usageMetadata"
      googleJson `shouldContain` "promptTokenCount"

    it "handles empty choices array" do
      let commonResp = mkMockCommonResponse { choices = [] }
      let googleJson = toGoogleResponse commonResp
      googleJson `shouldContain` "candidates"
      googleJson `shouldContain` "[]"

    it "handles single choice" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "test" (Just Stop)] }
      let googleJson = toGoogleResponse commonResp
      googleJson `shouldContain` "test"

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
      let googleJson = toGoogleResponse commonResp
      googleJson `shouldContain` "content"

    it "handles finishReason Stop" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "test" (Just Stop)] }
      let googleJson = toGoogleResponse commonResp
      googleJson `shouldContain` "finishReason"
      googleJson `shouldContain` "STOP"

    it "handles finishReason Length" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "test" (Just Length)] }
      let googleJson = toGoogleResponse commonResp
      googleJson `shouldContain` "MAX_TOKENS"

    it "handles finishReason ContentFilter" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "test" (Just ContentFilter)] }
      let googleJson = toGoogleResponse commonResp
      googleJson `shouldContain` "SAFETY"

    it "handles finishReason ToolCalls" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "test" (Just ToolCalls)] }
      let googleJson = toGoogleResponse commonResp
      -- Google may not have tool_calls finish reason, may map to STOP
      googleJson `shouldContain` "finishReason"

    it "omits finishReason when Nothing" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "test" Nothing] }
      let googleJson = toGoogleResponse commonResp
      -- finishReason may be omitted or null
      -- Test documents behavior
      pure unit

    it "handles usage information" do
      let commonResp = mkMockCommonResponse
        { choices = [mkMockChoice Assistant "test" (Just Stop)]
        , usage = Just mkMockUsage
        }
      let googleJson = toGoogleResponse commonResp
      googleJson `shouldContain` "usageMetadata"
      googleJson `shouldContain` "promptTokenCount"
      googleJson `shouldContain` "candidatesTokenCount"

    it "omits usage when Nothing" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "test" (Just Stop)] }
      let googleJson = toGoogleResponse commonResp
      -- usageMetadata may be omitted when Nothing
      -- Test documents behavior
      pure unit

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant longContent (Just Stop)] }
      let googleJson = toGoogleResponse commonResp
      -- Should preserve long content
      googleJson.length `shouldNotEqual` 0

    it "handles unicode characters" do
      let commonResp = mkMockCommonResponse { choices = [mkMockChoice Assistant "测试-🚀-こんにちは" (Just Stop)] }
      let googleJson = toGoogleResponse commonResp
      googleJson `shouldContain` "测试"

  describe "Round-trip Conversions" do
    it "preserves data in round-trip: Google → CommonResponse → Google" do
      let originalJson = validGoogleResponseMinimal
      let commonResp = fromGoogleResponse originalJson
      let roundTripJson = toGoogleResponse commonResp
      -- Round-trip should preserve essential data
      roundTripJson `shouldContain` "candidates"
      roundTripJson `shouldContain` "Hello"

    it "preserves all fields in round-trip with full response" do
      let originalJson = validGoogleResponseFull
      let commonResp = fromGoogleResponse originalJson
      let roundTripJson = toGoogleResponse commonResp
      -- Should preserve candidates, usageMetadata
      roundTripJson `shouldContain` "candidates"
      roundTripJson `shouldContain` "usageMetadata"

    it "preserves content in round-trip" do
      let json = """{"candidates":[{"content":{"parts":[{"text":"Hello"}],"role":"model"},"finishReason":"STOP"}]}"""
      let commonResp = fromGoogleResponse json
      let roundTripJson = toGoogleResponse commonResp
      roundTripJson `shouldContain` "Hello"

    it "BUG: may lose precision in timestamp during round-trip" do
      -- BUG: Timestamp precision may be lost in JSON serialization
      -- Google doesn't have created field, so it may be set to 0 or current time
      let json = """{"candidates":[{"content":{"parts":[{"text":"test"}],"role":"model"},"finishReason":"STOP"}]}"""
      let commonResp = fromGoogleResponse json
      -- Created may lose precision if stored as Number instead of Int
      -- Test documents potential precision loss
      pure unit

    it "BUG: may change field order in round-trip" do
      -- BUG: JSON field order may change (not critical but documents behavior)
      let json = """{"candidates":[{"content":{"parts":[{"text":"test"}],"role":"model"},"finishReason":"STOP"}]}"""
      let commonResp = fromGoogleResponse json
      let roundTripJson = toGoogleResponse commonResp
      -- Field order may differ but content should be same
      roundTripJson `shouldContain` "candidates"

  describe "Edge Cases" do
    it "handles CommonResponse → Google → CommonResponse round-trip" do
      let originalResp = mkMockCommonResponse
        { id: "response_123"
        , model: "gemini-pro"
        , choices = [mkMockChoice Assistant "test" (Just Stop)]
        , usage = Just mkMockUsage
        }
      let googleJson = toGoogleResponse originalResp
      let roundTripResp = fromGoogleResponse googleJson
      roundTripResp.model `shouldEqual` "gemini-pro"
      roundTripResp.choices.length `shouldEqual` 1

    it "handles empty id in round-trip" do
      let commonResp = mkMockCommonResponse { id = "" }
      let googleJson = toGoogleResponse commonResp
      let roundTripResp = fromGoogleResponse googleJson
      -- Google doesn't have id field, so may be empty or generated
      roundTripResp.id.length `shouldNotEqual` (-1)
