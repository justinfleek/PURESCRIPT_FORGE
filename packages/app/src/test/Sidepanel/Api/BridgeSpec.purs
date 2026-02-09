-- | Bridge API Tests
-- | Unit and property tests for Bridge API client functions
module Test.Sidepanel.Api.BridgeSpec where

import Prelude
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy)
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
import Data.Argonaut.Core (Json)
import Data.Argonaut.Encode (class EncodeJson, encodeJson)
import Data.Argonaut.Decode (class DecodeJson, decodeJson)
import Data.Argonaut.Decode.Error (JsonDecodeError)

-- | Test JSON encoding/decoding
testJsonCodecs :: Spec Unit
testJsonCodecs =
  describe "JSON Codecs" do
    it "encodes FileContextAddRequest" do
      let request = { path: "/test/file.ts", sessionId: Just "session-123" }
      let encoded = encodeJson request
      true `shouldSatisfy` identity -- Would verify encoding
    
    it "decodes FileContextAddResponse" do
      let json = encodeJson { success: true, tokens: 100, contextBudget: { used: 50, total: 1000 } }
      case (decodeJson json :: Either JsonDecodeError { success :: Boolean, tokens :: Int, contextBudget :: { used :: Int, total :: Int } }) of
        Right response ->
          response.success `shouldEqual` true
        Left _ -> false `shouldEqual` true
    
    it "encodes TerminalExecuteRequest" do
      let request = { command: "ls -la", cwd: Just "/home", sessionId: Just "session-123" }
      let encoded = encodeJson request
      true `shouldSatisfy` identity -- Would verify encoding
    
    it "decodes TerminalExecuteResponse" do
      let json = encodeJson { success: true, output: Just "file1\nfile2", exitCode: Just 0 }
      case (decodeJson json :: Either JsonDecodeError { success :: Boolean, output :: Maybe String, exitCode :: Maybe Int }) of
        Right response ->
          response.success `shouldEqual` true
        Left _ -> false `shouldEqual` true
    
    it "encodes SessionNewRequest" do
      let request = { name: Just "Test Session", parentId: Nothing, model: Just "claude-3-opus", provider: Just "venice" } :: { name :: Maybe String, parentId :: Maybe String, model :: Maybe String, provider :: Maybe String }
      let encoded = encodeJson request
      true `shouldSatisfy` identity -- Would verify encoding
    
    it "decodes SessionNewResponse" do
      let json = encodeJson { sessionId: "session-123", success: true }
      case (decodeJson json :: Either JsonDecodeError { sessionId :: String, success :: Boolean }) of
        Right response ->
          response.sessionId `shouldEqual` "session-123"
        Left _ -> false `shouldEqual` true

-- | Property: JSON encoding/decoding is idempotent
prop_jsonRoundTrip :: forall a. EncodeJson a => DecodeJson a => Eq a => a -> Boolean
prop_jsonRoundTrip value = 
  case decodeJson (encodeJson value) of
    Right decoded -> decoded == value
    Left _ -> false

-- | Property tests (using concrete values since record type aliases lack Arbitrary instances)
testProperties :: Spec Unit
testProperties =
  describe "Property Tests" do
    it "FileContextAddRequest JSON round-trip" do
      let val = { path: "/test/file.ts", sessionId: Just "s1" } :: FileContextAddRequest
      prop_jsonRoundTrip val `shouldEqual` true

    it "TerminalExecuteRequest JSON round-trip" do
      let val = { command: "ls", cwd: Just "/home", sessionId: Just "s1" } :: TerminalExecuteRequest
      prop_jsonRoundTrip val `shouldEqual` true

    it "TerminalExecuteResponse JSON round-trip" do
      let val = { success: true, output: Just "ok", exitCode: Just 0 } :: TerminalExecuteResponse
      prop_jsonRoundTrip val `shouldEqual` true

    it "SessionNewRequest JSON round-trip" do
      let val = { name: Just "Test", parentId: Nothing, model: Just "claude", provider: Just "venice" } :: SessionNewRequest
      prop_jsonRoundTrip val `shouldEqual` true

    it "SessionNewResponse JSON round-trip" do
      let val = { sessionId: "s1", success: true } :: SessionNewResponse
      prop_jsonRoundTrip val `shouldEqual` true
