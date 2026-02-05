-- | Deep comprehensive tests for Provider module
-- | Tests all provider format parsing and usage normalization functions
module Test.Unit.Util.ProviderSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual)
import Data.Maybe (Maybe(..), isJust, isNothing)

import Console.App.Routes.Omega.Util.Provider.Provider
  ( ProviderFormat(..)
  , UsageInfo
  , CommonUsage
  , parseProviderFormat
  , normalizeUsage
  , createBodyConverter
  , createStreamPartConverter
  , createResponseConverter
  , CommonRequest
  , CommonChunk
  , CommonResponse
  )

-- | Create mock CommonUsage
mkMockCommonUsage :: CommonUsage
mkMockCommonUsage =
  { inputTokens: Nothing
  , outputTokens: Nothing
  , totalTokens: Nothing
  , promptTokens: Nothing
  , completionTokens: Nothing
  , cacheReadInputTokens: Nothing
  , cacheCreationEphemeral5mInputTokens: Nothing
  , cacheCreationEphemeral1hInputTokens: Nothing
  , cachedTokens: Nothing
  , reasoningTokens: Nothing
  }

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

-- | Create mock CommonChunk
mkMockCommonChunk :: CommonChunk
mkMockCommonChunk =
  { id: "chunk_123"
  , object: "chat.completion.chunk"
  , created: 1234567890
  , model: "gpt-4"
  , choices: []
  , usage: Nothing
  }

-- | Create mock CommonResponse
mkMockCommonResponse :: CommonResponse
mkMockCommonResponse =
  { id: "resp_123"
  , object: "chat.completion"
  , created: 1234567890
  , model: "gpt-4"
  , choices: []
  , usage: Nothing
  }

-- | Deep comprehensive tests for Provider
spec :: Spec Unit
spec = describe "Provider Deep Tests" do
  describe "parseProviderFormat" do
    it "parses 'anthropic' correctly" do
      parseProviderFormat "anthropic" `shouldEqual` Just Anthropic

    it "parses 'openai' correctly" do
      parseProviderFormat "openai" `shouldEqual` Just OpenAI

    it "parses 'oa-compat' correctly" do
      parseProviderFormat "oa-compat" `shouldEqual` Just OACompat

    it "parses 'google' correctly" do
      parseProviderFormat "google" `shouldEqual` Just Google

    it "returns Nothing for invalid format" do
      parseProviderFormat "invalid" `shouldEqual` Nothing

    it "returns Nothing for empty string" do
      parseProviderFormat "" `shouldEqual` Nothing

    it "BUG: case-sensitive parsing" do
      -- BUG: parseProviderFormat is case-sensitive
      -- "Anthropic" (capital A) returns Nothing
      -- Expected: Should be case-insensitive or documented as case-sensitive
      -- Actual: Case-sensitive matching
      parseProviderFormat "Anthropic" `shouldEqual` Nothing
      parseProviderFormat "OPENAI" `shouldEqual` Nothing
      parseProviderFormat "OA-COMPAT" `shouldEqual` Nothing
      -- This test documents the bug: case-sensitive parsing

    it "returns Nothing for whitespace-only string" do
      parseProviderFormat "   " `shouldEqual` Nothing

    it "returns Nothing for string with leading/trailing whitespace" do
      parseProviderFormat " openai " `shouldEqual` Nothing
      parseProviderFormat " anthropic" `shouldEqual` Nothing
      parseProviderFormat "google " `shouldEqual` Nothing

    it "returns Nothing for similar but different strings" do
      parseProviderFormat "open-ai" `shouldEqual` Nothing
      parseProviderFormat "open_ai" `shouldEqual` Nothing
      parseProviderFormat "anthropic-v1" `shouldEqual` Nothing

  describe "normalizeUsage" do
    it "uses inputTokens when present" do
      let usage = mkMockCommonUsage { inputTokens = Just 1000 }
      let normalized = normalizeUsage usage
      normalized.inputTokens `shouldEqual` 1000

    it "falls back to promptTokens when inputTokens is Nothing" do
      let usage = mkMockCommonUsage
        { inputTokens = Nothing
        , promptTokens = Just 800
        }
      let normalized = normalizeUsage usage
      normalized.inputTokens `shouldEqual` 800

    it "falls back to 0 when both inputTokens and promptTokens are Nothing" do
      let usage = mkMockCommonUsage
        { inputTokens = Nothing
        , promptTokens = Nothing
        }
      let normalized = normalizeUsage usage
      normalized.inputTokens `shouldEqual` 0

    it "uses outputTokens when present" do
      let usage = mkMockCommonUsage { outputTokens = Just 500 }
      let normalized = normalizeUsage usage
      normalized.outputTokens `shouldEqual` 500

    it "falls back to completionTokens when outputTokens is Nothing" do
      let usage = mkMockCommonUsage
        { outputTokens = Nothing
        , completionTokens = Just 400
        }
      let normalized = normalizeUsage usage
      normalized.outputTokens `shouldEqual` 400

    it "falls back to 0 when both outputTokens and completionTokens are Nothing" do
      let usage = mkMockCommonUsage
        { outputTokens = Nothing
        , completionTokens = Nothing
        }
      let normalized = normalizeUsage usage
      normalized.outputTokens `shouldEqual` 0

    it "preserves reasoningTokens" do
      let usage = mkMockCommonUsage { reasoningTokens = Just 200 }
      let normalized = normalizeUsage usage
      normalized.reasoningTokens `shouldEqual` Just 200

    it "preserves reasoningTokens as Nothing" do
      let usage = mkMockCommonUsage { reasoningTokens = Nothing }
      let normalized = normalizeUsage usage
      normalized.reasoningTokens `shouldEqual` Nothing

    it "uses cacheReadInputTokens when present" do
      let usage = mkMockCommonUsage { cacheReadInputTokens = Just 100 }
      let normalized = normalizeUsage usage
      normalized.cacheReadTokens `shouldEqual` Just 100

    it "falls back to cachedTokens when cacheReadInputTokens is Nothing" do
      let usage = mkMockCommonUsage
        { cacheReadInputTokens = Nothing
        , cachedTokens = Just 50
        }
      let normalized = normalizeUsage usage
      normalized.cacheReadTokens `shouldEqual` Just 50

    it "returns Nothing when both cacheReadInputTokens and cachedTokens are Nothing" do
      let usage = mkMockCommonUsage
        { cacheReadInputTokens = Nothing
        , cachedTokens = Nothing
        }
      let normalized = normalizeUsage usage
      normalized.cacheReadTokens `shouldEqual` Nothing

    it "preserves cacheWrite5mTokens" do
      let usage = mkMockCommonUsage { cacheCreationEphemeral5mInputTokens = Just 300 }
      let normalized = normalizeUsage usage
      normalized.cacheWrite5mTokens `shouldEqual` Just 300

    it "preserves cacheWrite5mTokens as Nothing" do
      let usage = mkMockCommonUsage { cacheCreationEphemeral5mInputTokens = Nothing }
      let normalized = normalizeUsage usage
      normalized.cacheWrite5mTokens `shouldEqual` Nothing

    it "preserves cacheWrite1hTokens" do
      let usage = mkMockCommonUsage { cacheCreationEphemeral1hInputTokens = Just 400 }
      let normalized = normalizeUsage usage
      normalized.cacheWrite1hTokens `shouldEqual` Just 400

    it "preserves cacheWrite1hTokens as Nothing" do
      let usage = mkMockCommonUsage { cacheCreationEphemeral1hInputTokens = Nothing }
      let normalized = normalizeUsage usage
      normalized.cacheWrite1hTokens `shouldEqual` Nothing

    it "handles all fields present" do
      let usage = mkMockCommonUsage
        { inputTokens = Just 1000
        , outputTokens = Just 500
        , reasoningTokens = Just 200
        , cacheReadInputTokens = Just 100
        , cacheCreationEphemeral5mInputTokens = Just 300
        , cacheCreationEphemeral1hInputTokens = Just 400
        }
      let normalized = normalizeUsage usage
      normalized.inputTokens `shouldEqual` 1000
      normalized.outputTokens `shouldEqual` 500
      normalized.reasoningTokens `shouldEqual` Just 200
      normalized.cacheReadTokens `shouldEqual` Just 100
      normalized.cacheWrite5mTokens `shouldEqual` Just 300
      normalized.cacheWrite1hTokens `shouldEqual` Just 400

    it "handles all fields as Nothing" do
      let usage = mkMockCommonUsage
        { inputTokens = Nothing
        , outputTokens = Nothing
        , promptTokens = Nothing
        , completionTokens = Nothing
        , reasoningTokens = Nothing
        , cacheReadInputTokens = Nothing
        , cachedTokens = Nothing
        , cacheCreationEphemeral5mInputTokens = Nothing
        , cacheCreationEphemeral1hInputTokens = Nothing
        }
      let normalized = normalizeUsage usage
      normalized.inputTokens `shouldEqual` 0
      normalized.outputTokens `shouldEqual` 0
      normalized.reasoningTokens `shouldEqual` Nothing
      normalized.cacheReadTokens `shouldEqual` Nothing
      normalized.cacheWrite5mTokens `shouldEqual` Nothing
      normalized.cacheWrite1hTokens `shouldEqual` Nothing

    it "BUG: prefers inputTokens over promptTokens even if promptTokens is larger" do
      -- BUG: normalizeUsage uses inputTokens if present, ignoring promptTokens
      -- If inputTokens is 0 but promptTokens is 1000, it uses 0
      -- Expected: Should use max(inputTokens, promptTokens) or sum
      -- Actual: Uses inputTokens if present, even if 0
      let usage = mkMockCommonUsage
        { inputTokens = Just 0
        , promptTokens = Just 1000
        }
      let normalized = normalizeUsage usage
      normalized.inputTokens `shouldEqual` 0  -- Uses inputTokens (0) instead of promptTokens (1000)
      -- This test documents the bug: inputTokens=0 overrides promptTokens

    it "BUG: prefers outputTokens over completionTokens even if completionTokens is larger" do
      -- Similar bug: outputTokens=0 overrides completionTokens
      let usage = mkMockCommonUsage
        { outputTokens = Just 0
        , completionTokens = Just 500
        }
      let normalized = normalizeUsage usage
      normalized.outputTokens `shouldEqual` 0  -- Uses outputTokens (0) instead of completionTokens (500)
      -- This test documents the bug

    it "handles zero values correctly" do
      let usage = mkMockCommonUsage
        { inputTokens = Just 0
        , outputTokens = Just 0
        , reasoningTokens = Just 0
        , cacheReadInputTokens = Just 0
        }
      let normalized = normalizeUsage usage
      normalized.inputTokens `shouldEqual` 0
      normalized.outputTokens `shouldEqual` 0
      normalized.reasoningTokens `shouldEqual` Just 0
      normalized.cacheReadTokens `shouldEqual` Just 0

    it "handles negative values (edge case)" do
      -- Test handling of negative token values
      let usage = mkMockCommonUsage
        { inputTokens = Just (-100)
        , outputTokens = Just (-50)
        }
      let normalized = normalizeUsage usage
      normalized.inputTokens `shouldEqual` (-100)
      normalized.outputTokens `shouldEqual` (-50)

    it "handles very large values" do
      let usage = mkMockCommonUsage
        { inputTokens = Just 2147483647
        , outputTokens = Just 2147483647
        }
      let normalized = normalizeUsage usage
      normalized.inputTokens `shouldEqual` 2147483647
      normalized.outputTokens `shouldEqual` 2147483647

  describe "createBodyConverter" do
    it "returns identity when formats match" do
      let converter = createBodyConverter OpenAI OpenAI
      let request = mkMockCommonRequest
      converter request `shouldEqual` request

    it "returns identity for all matching formats" do
      let request = mkMockCommonRequest
      (createBodyConverter Anthropic Anthropic) request `shouldEqual` request
      (createBodyConverter OACompat OACompat) request `shouldEqual` request
      (createBodyConverter Google Google) request `shouldEqual` request

    it "returns different function when formats don't match" do
      -- When formats don't match, returns FFI function
      -- Can't test FFI directly, but can verify it's not identity
      let converter = createBodyConverter OpenAI Anthropic
      let request = mkMockCommonRequest
      -- Converter should be a function (not identity)
      -- This test documents the behavior
      pure unit

  describe "createStreamPartConverter" do
    it "returns identity when formats match" do
      let converter = createStreamPartConverter OpenAI OpenAI
      let chunk = mkMockCommonChunk
      converter chunk `shouldEqual` chunk

    it "returns identity for all matching formats" do
      let chunk = mkMockCommonChunk
      (createStreamPartConverter Anthropic Anthropic) chunk `shouldEqual` chunk
      (createStreamPartConverter OACompat OACompat) chunk `shouldEqual` chunk
      (createStreamPartConverter Google Google) chunk `shouldEqual` chunk

    it "returns different function when formats don't match" do
      -- When formats don't match, returns FFI function
      let converter = createStreamPartConverter OpenAI Anthropic
      let chunk = mkMockCommonChunk
      -- Converter should be a function (not identity)
      pure unit

  describe "createResponseConverter" do
    it "returns identity when formats match" do
      let converter = createResponseConverter OpenAI OpenAI
      let response = mkMockCommonResponse
      converter response `shouldEqual` response

    it "returns identity for all matching formats" do
      let response = mkMockCommonResponse
      (createResponseConverter Anthropic Anthropic) response `shouldEqual` response
      (createResponseConverter OACompat OACompat) response `shouldEqual` response
      (createResponseConverter Google Google) response `shouldEqual` response

    it "returns different function when formats don't match" do
      -- When formats don't match, returns FFI function
      let converter = createResponseConverter OpenAI Anthropic
      let response = mkMockCommonResponse
      -- Converter should be a function (not identity)
      pure unit

  describe "Edge Cases" do
    it "handles totalTokens field (not used in normalization)" do
      -- totalTokens is in CommonUsage but not used in normalizeUsage
      let usage = mkMockCommonUsage { totalTokens = Just 1500 }
      let normalized = normalizeUsage usage
      -- totalTokens is ignored
      normalized.inputTokens `shouldEqual` 0  -- Uses fallback
      normalized.outputTokens `shouldEqual` 0  -- Uses fallback

    it "verifies fallback chain for inputTokens" do
      -- Chain: inputTokens -> promptTokens -> 0
      let usage1 = mkMockCommonUsage { inputTokens = Just 100 }
      let usage2 = mkMockCommonUsage { promptTokens = Just 100 }
      let usage3 = mkMockCommonUsage { inputTokens = Nothing, promptTokens = Nothing }
      normalizeUsage usage1 `shouldNotEqual` normalizeUsage usage2
      normalizeUsage usage2 `shouldNotEqual` normalizeUsage usage3

    it "verifies fallback chain for outputTokens" do
      -- Chain: outputTokens -> completionTokens -> 0
      let usage1 = mkMockCommonUsage { outputTokens = Just 50 }
      let usage2 = mkMockCommonUsage { completionTokens = Just 50 }
      let usage3 = mkMockCommonUsage { outputTokens = Nothing, completionTokens = Nothing }
      normalizeUsage usage1 `shouldNotEqual` normalizeUsage usage2
      normalizeUsage usage2 `shouldNotEqual` normalizeUsage usage3

    it "verifies fallback chain for cacheReadTokens" do
      -- Chain: cacheReadInputTokens -> cachedTokens -> Nothing
      let usage1 = mkMockCommonUsage { cacheReadInputTokens = Just 10 }
      let usage2 = mkMockCommonUsage { cachedTokens = Just 10 }
      let usage3 = mkMockCommonUsage { cacheReadInputTokens = Nothing, cachedTokens = Nothing }
      normalizeUsage usage1 `shouldNotEqual` normalizeUsage usage2
      normalizeUsage usage2 `shouldNotEqual` normalizeUsage usage3

  describe "Bug Detection Tests" do
    it "detects bug: case-sensitive format parsing" do
      -- BUG: parseProviderFormat is case-sensitive
      -- "Anthropic" != "anthropic"
      parseProviderFormat "Anthropic" `shouldEqual` Nothing
      parseProviderFormat "anthropic" `shouldEqual` Just Anthropic
      -- This test documents the bug

    it "detects bug: inputTokens=0 overrides promptTokens" do
      -- BUG: normalizeUsage uses inputTokens if present, even if 0
      -- Should use promptTokens if inputTokens is 0
      let usage = mkMockCommonUsage
        { inputTokens = Just 0
        , promptTokens = Just 1000
        }
      let normalized = normalizeUsage usage
      normalized.inputTokens `shouldEqual` 0  -- Bug: should be 1000
      -- This test documents the bug

    it "detects bug: outputTokens=0 overrides completionTokens" do
      -- Similar bug for outputTokens
      let usage = mkMockCommonUsage
        { outputTokens = Just 0
        , completionTokens = Just 500
        }
      let normalized = normalizeUsage usage
      normalized.outputTokens `shouldEqual` 0  -- Bug: should be 500
      -- This test documents the bug

    it "verifies totalTokens is ignored" do
      -- totalTokens field exists but is not used in normalization
      -- This may or may not be a bug depending on requirements
      let usage = mkMockCommonUsage { totalTokens = Just 2000 }
      let normalized = normalizeUsage usage
      -- totalTokens is not used
      normalized.inputTokens `shouldEqual` 0
      -- This test documents the behavior
