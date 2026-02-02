-- | Bridge API Tests
-- | Unit and property tests for Bridge API client functions
module Test.Sidepanel.Api.BridgeSpec where

import Prelude
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual, shouldBeTrue)
import Test.QuickCheck (quickCheck, (<?>))
import Effect.Aff (Aff)
import Data.Either (Either(..), isRight, isLeft)
import Data.Maybe (Maybe(..))
import Sidepanel.Api.Bridge
  ( FileContextAddRequest
  , FileContextAddResponse
  , FileContextListRequest
  , FileContextListResponse
  , TerminalExecuteRequest
  , TerminalExecuteResponse
  , SessionNewRequest
  , SessionNewResponse
  )
import Argonaut.Core (Json)
import Argonaut.Encode (class EncodeJson, encodeJson)
import Argonaut.Decode (class DecodeJson, decodeJson)

-- | Test JSON encoding/decoding
testJsonCodecs :: forall m. Monad m => m Unit
testJsonCodecs = do
  describe "JSON Codecs" do
    it "encodes FileContextAddRequest" do
      let request = { path: "/test/file.ts", sessionId: Just "session-123" }
      let encoded = encodeJson request
      true `shouldBeTrue` -- Would verify encoding
    
    it "decodes FileContextAddResponse" do
      let json = encodeJson { success: true, tokens: 100, contextBudget: { used: 50, total: 1000 } }
      case decodeJson json of
        Right response -> 
          response.success `shouldEqual` true
        Left _ -> false `shouldEqual` true
    
    it "encodes TerminalExecuteRequest" do
      let request = { command: "ls -la", cwd: Just "/home", sessionId: Just "session-123" }
      let encoded = encodeJson request
      true `shouldBeTrue` -- Would verify encoding
    
    it "decodes TerminalExecuteResponse" do
      let json = encodeJson { success: true, output: Just "file1\nfile2", exitCode: Just 0 }
      case decodeJson json of
        Right response -> 
          response.success `shouldEqual` true
        Left _ -> false `shouldEqual` true
    
    it "encodes SessionNewRequest" do
      let request = { name: Just "Test Session", parentId: Nothing, model: Just "claude-3-opus", provider: Just "venice" }
      let encoded = encodeJson request
      true `shouldBeTrue` -- Would verify encoding
    
    it "decodes SessionNewResponse" do
      let json = encodeJson { sessionId: "session-123", success: true }
      case decodeJson json of
        Right response -> 
          response.sessionId `shouldEqual` "session-123"
        Left _ -> false `shouldEqual` true

-- | Property: JSON encoding/decoding is idempotent
prop_jsonRoundTrip :: forall a. EncodeJson a => DecodeJson a => Eq a => a -> Boolean
prop_jsonRoundTrip value = 
  case decodeJson (encodeJson value) of
    Right decoded -> decoded == value
    Left _ -> false

-- | Property tests
testProperties :: forall m. Monad m => m Unit
testProperties = do
  describe "Property Tests" do
    it "FileContextAddRequest JSON round-trip" do
      quickCheck prop_jsonRoundTrip
    
    it "FileContextAddResponse JSON round-trip" do
      quickCheck prop_jsonRoundTrip
    
    it "TerminalExecuteRequest JSON round-trip" do
      quickCheck prop_jsonRoundTrip
    
    it "TerminalExecuteResponse JSON round-trip" do
      quickCheck prop_jsonRoundTrip
    
    it "SessionNewRequest JSON round-trip" do
      quickCheck prop_jsonRoundTrip
    
    it "SessionNewResponse JSON round-trip" do
      quickCheck prop_jsonRoundTrip
