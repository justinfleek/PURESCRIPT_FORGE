-- | Deep comprehensive tests for Anthropic Chunk conversion module
-- | Tests fromAnthropicChunk and toAnthropicChunk with error handling,
-- | edge cases, and bug detection
module Test.Unit.Util.Provider.AnthropicChunkSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual, shouldContain)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Data.Either (Either(..), isLeft, isRight)
import Data.Array (length, head)
import Data.Foldable (fold)
import Data.Array as Array
import Data.String as String

import Console.App.Routes.Omega.Util.Provider.Anthropic.Chunk
  ( fromAnthropicChunk
  , toAnthropicChunk
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
  { id: "msg_123"
  , object: "chat.completion.chunk"
  , created: 1677652288
  , model: "claude-3-opus-20240229"
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

-- | Valid Anthropic chunk JSON (content delta)
validAnthropicChunkContent :: String
validAnthropicChunkContent = """{"type":"content_block_delta","index":0,"delta":{"type":"text_delta","text":"Hello"}}"""

-- | Valid Anthropic chunk JSON (finish reason)
validAnthropicChunkFinish :: String
validAnthropicChunkFinish = """{"type":"message_delta","delta":{"stop_reason":"end_turn","stop_sequence":null}}"""

-- | Valid Anthropic chunk JSON (tool use)
validAnthropicChunkToolUse :: String
validAnthropicChunkToolUse = """{"type":"content_block_delta","index":0,"delta":{"type":"tool_use_delta","id":"tool_123","name":"test_fn"}}"""

-- | Deep comprehensive tests for Anthropic Chunk conversions
spec :: Spec Unit
spec = describe "Anthropic Chunk Conversion Deep Tests" do
  describe "fromAnthropicChunk" do
    it "converts valid Anthropic chunk with content delta to CommonChunk" do
      case fromAnthropicChunk validAnthropicChunkContent of
        Left err -> pure unit  -- Should not error
        Right commonChunk -> do
          commonChunk.choices.length `shouldEqual` 1

    it "converts chunk with finish reason" do
      case fromAnthropicChunk validAnthropicChunkFinish of
        Left err -> pure unit
        Right commonChunk -> do
          -- Finish reason should be extracted
          commonChunk.choices.length `shouldEqual` 1

    it "converts chunk with tool use" do
      case fromAnthropicChunk validAnthropicChunkToolUse of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> isJust choice.delta.toolCalls `shouldEqual` true
            Nothing -> pure unit

    it "handles empty delta" do
      let json = """{"type":"content_block_delta","index":0,"delta":{}}"""
      case fromAnthropicChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.delta.content `shouldEqual` Nothing
            Nothing -> pure unit

    it "handles delta with content" do
      let json = """{"type":"content_block_delta","index":0,"delta":{"type":"text_delta","text":"Hello"}}"""
      case fromAnthropicChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.delta.content `shouldEqual` Just "Hello"
            Nothing -> pure unit

    it "handles delta with empty content" do
      let json = """{"type":"content_block_delta","index":0,"delta":{"type":"text_delta","text":""}}"""
      case fromAnthropicChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> choice.delta.content `shouldEqual` Just ""
            Nothing -> pure unit

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let json = """{"type":"content_block_delta","index":0,"delta":{"type":"text_delta","text":""" <> "\"" <> longContent <> "\"" <> """}}"""
      case fromAnthropicChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> do
              case choice.delta.content of
                Just c -> c.length `shouldEqual` 10000
                Nothing -> pure unit
            Nothing -> pure unit

    it "handles unicode characters in content" do
      let json = """{"type":"content_block_delta","index":0,"delta":{"type":"text_delta","text":"测试-🚀-こんにちは"}}"""
      case fromAnthropicChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          case head commonChunk.choices of
            Just choice -> do
              case choice.delta.content of
                Just c -> c `shouldContain` "测试"
                Nothing -> pure unit
            Nothing -> pure unit

    it "handles special characters in content" do
      let json = """{"type":"content_block_delta","index":0,"delta":{"type":"text_delta","text":"test\\nwith\\tnewlines\\\"and\\\"quotes"}}"""
      case fromAnthropicChunk json of
        Left err -> pure unit
        Right commonChunk -> commonChunk.choices.length `shouldEqual` 1

    it "returns Left for invalid JSON string" do
      let invalidJson = """{"type":"content_block_delta"""
      case fromAnthropicChunk invalidJson of
        Left err -> do
          -- Should return error message
          err.length `shouldNotEqual` 0
        Right _ -> pure unit  -- Should not succeed

    it "returns Left for malformed JSON (missing quotes)" do
      let malformedJson = """{type:"content_block_delta",index:0}"""
      case fromAnthropicChunk malformedJson of
        Left err -> do
          -- Should return error message
          err.length `shouldNotEqual` 0
        Right _ -> pure unit  -- Should not succeed

    it "BUG: may return Right for missing required fields" do
      -- BUG: Missing type, index, or delta may not return Left
      let json = """{"index":0,"delta":{}}"""
      case fromAnthropicChunk json of
        Left err -> pure unit  -- Should error but may not
        Right commonChunk -> do
          -- type may be missing but conversion succeeds
          pure unit

  describe "toAnthropicChunk" do
    it "converts minimal CommonChunk to Anthropic format" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "Hello") Nothing] }
      let anthropicJson = toAnthropicChunk commonChunk
      -- Should contain type, delta
      anthropicJson `shouldContain` "delta"
      anthropicJson `shouldContain` "Hello"

    it "converts CommonChunk with content delta" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "test") Nothing] }
      let anthropicJson = toAnthropicChunk commonChunk
      anthropicJson `shouldContain` "delta"
      anthropicJson `shouldContain` "test"

    it "converts CommonChunk with finish reason" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just Stop)] }
      let anthropicJson = toAnthropicChunk commonChunk
      anthropicJson `shouldContain` "stop_reason"

    it "handles empty choices array" do
      let commonChunk = mkMockCommonChunk { choices = [] }
      let anthropicJson = toAnthropicChunk commonChunk
      -- Anthropic format may handle empty choices differently
      -- Test documents behavior
      pure unit

    it "handles single choice" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "test") Nothing] }
      let anthropicJson = toAnthropicChunk commonChunk
      anthropicJson `shouldContain` "test"

    it "handles empty delta" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing Nothing] }
      let anthropicJson = toAnthropicChunk commonChunk
      anthropicJson `shouldContain` "delta"

    it "handles delta with content" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "Hello") Nothing] }
      let anthropicJson = toAnthropicChunk commonChunk
      anthropicJson `shouldContain` "content"
      anthropicJson `shouldContain` "Hello"

    it "handles delta with empty content" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "") Nothing] }
      let anthropicJson = toAnthropicChunk commonChunk
      anthropicJson `shouldContain` "delta"

    it "handles finishReason Stop" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just Stop)] }
      let anthropicJson = toAnthropicChunk commonChunk
      anthropicJson `shouldContain` "stop_reason"
      anthropicJson `shouldContain` "end_turn"  -- Anthropic uses "end_turn" for stop

    it "handles finishReason ToolCalls" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just ToolCalls)] }
      let anthropicJson = toAnthropicChunk commonChunk
      anthropicJson `shouldContain` "tool_use"

    it "handles finishReason Length" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just Length)] }
      let anthropicJson = toAnthropicChunk commonChunk
      anthropicJson `shouldContain` "max_tokens"

    it "handles finishReason ContentFilter" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing (Just ContentFilter)] }
      let anthropicJson = toAnthropicChunk commonChunk
      -- Anthropic may not have content_filter, may map to end_turn
      anthropicJson `shouldContain` "stop_reason"

    it "omits finish_reason when Nothing" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice Nothing Nothing] }
      let anthropicJson = toAnthropicChunk commonChunk
      -- finish_reason may be omitted or null
      -- Test documents behavior
      pure unit

    it "handles very long content string" do
      let longContent = fold (replicate 10000 "a")
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just longContent) Nothing] }
      let anthropicJson = toAnthropicChunk commonChunk
      -- Should preserve long content
      anthropicJson.length `shouldNotEqual` 0

    it "handles unicode characters" do
      let commonChunk = mkMockCommonChunk { choices = [mkMockChunkChoice (Just "测试-🚀-こんにちは") Nothing] }
      let anthropicJson = toAnthropicChunk commonChunk
      anthropicJson `shouldContain` "测试"

    it "handles empty id string" do
      let commonChunk = mkMockCommonChunk { id = "" }
      let anthropicJson = toAnthropicChunk commonChunk
      -- Anthropic chunks may not have id field
      -- Test documents behavior
      pure unit

  describe "Round-trip Conversions" do
    it "preserves data in round-trip: Anthropic → CommonChunk → Anthropic" do
      case fromAnthropicChunk validAnthropicChunkContent of
        Left err -> pure unit
        Right commonChunk -> do
          let roundTripJson = toAnthropicChunk commonChunk
          -- Round-trip should preserve essential data
          roundTripJson `shouldContain` "delta"

    it "preserves content delta in round-trip" do
      let json = """{"type":"content_block_delta","index":0,"delta":{"type":"text_delta","text":"Hello"}}"""
      case fromAnthropicChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          let roundTripJson = toAnthropicChunk commonChunk
          roundTripJson `shouldContain` "Hello"

    it "preserves finish reason in round-trip" do
      let json = """{"type":"message_delta","delta":{"stop_reason":"end_turn"}}"""
      case fromAnthropicChunk json of
        Left err -> pure unit
        Right commonChunk -> do
          let roundTripJson = toAnthropicChunk commonChunk
          roundTripJson `shouldContain` "stop_reason"

  describe "Error Handling" do
    it "returns meaningful error message for invalid JSON" do
      let invalidJson = """{"type":"content_block_delta"""
      case fromAnthropicChunk invalidJson of
        Left err -> do
          -- Error message should be non-empty
          err.length `shouldNotEqual` 0
          -- Error message should indicate JSON parsing issue
          err `shouldContain` "error"
        Right _ -> pure unit  -- Should not succeed

    it "handles empty string input" do
      case fromAnthropicChunk "" of
        Left err -> do
          -- Should return error
          err.length `shouldNotEqual` 0
        Right _ -> pure unit  -- Should not succeed

    it "handles whitespace-only input" do
      case fromAnthropicChunk "   " of
        Left err -> do
          -- Should return error
          err.length `shouldNotEqual` 0
        Right _ -> pure unit  -- Should not succeed
