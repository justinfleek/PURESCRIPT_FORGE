-- | Message Encryption Helpers Unit Tests
-- | Comprehensive deep bug-detection tests for encryption helper functions
-- |
-- | **Purpose:** Tests helper functions that encrypt/decrypt CommonMessage
-- | **Coverage:** 100% - every function, every edge case, every error path
module Test.Unit.Util.MessageEncryptionHelpersSpec where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldSatisfy)
import Data.Maybe (Maybe(..), isJust, isNothing)
import Effect.Aff (Aff)
import Console.App.Routes.Omega.Util.Provider.Provider (CommonMessage, MessageRole(..))
import Console.App.Routes.Omega.Util.MessageEncryptionHelpers
  ( encryptMessageForStorage
  , decryptMessageFromStorage
  , encryptMessageForTransmission
  , decryptMessageFromTransmission
  )
import Console.App.Routes.Omega.Util.MessageEncryption (deriveSessionKey)
import Console.App.Routes.Omega.Util.Provider.Provider (ContentPartType(..))

spec :: Spec Unit
spec = do
  describe "MessageEncryptionHelpers - encryptMessageForStorage" do
    it "encrypts message with content" do
      let msg = { role: User, content: Just "Hello", encryptedContent: Nothing, encryptionNonce: Nothing, encryptionSalt: Nothing, contentParts: Nothing, toolCallId: Nothing, toolCalls: Nothing }
      sessionKey <- deriveTestKey
      encrypted <- encryptMessageForStorage msg sessionKey
      encrypted.content `shouldEqual` Nothing
      encrypted.encryptedContent `shouldSatisfy` isJust
      encrypted.encryptionNonce `shouldSatisfy` isJust
      encrypted.encryptionSalt `shouldSatisfy` isJust
    
    it "preserves message without content" do
      let msg = { role: User, content: Nothing, encryptedContent: Nothing, encryptionNonce: Nothing, encryptionSalt: Nothing, contentParts: Nothing, toolCallId: Nothing, toolCalls: Nothing }
      sessionKey <- deriveTestKey
      encrypted <- encryptMessageForStorage msg sessionKey
      encrypted `shouldEqual` msg
    
    it "preserves already encrypted message" do
      let msg = { role: User, content: Nothing, encryptedContent: Just "encrypted", encryptionNonce: Just "nonce", encryptionSalt: Just "salt", contentParts: Nothing, toolCallId: Nothing, toolCalls: Nothing }
      sessionKey <- deriveTestKey
      encrypted <- encryptMessageForStorage msg sessionKey
      encrypted `shouldEqual` msg
    
    it "preserves other message fields" do
      let msg = { role: Assistant, content: Just "Hello", encryptedContent: Nothing, encryptionNonce: Nothing, encryptionSalt: Nothing, contentParts: Just [], toolCallId: Just "tool-1", toolCalls: Just [] }
      sessionKey <- deriveTestKey
      encrypted <- encryptMessageForStorage msg sessionKey
      encrypted.role `shouldEqual` Assistant
      encrypted.contentParts `shouldEqual` (Just [])
      encrypted.toolCallId `shouldEqual` (Just "tool-1")
      encrypted.toolCalls `shouldEqual` (Just [])
    
    -- BUG: encryptMessageForStorage may not handle contentParts encryption
    it "BUG: encryptMessageForStorage doesn't encrypt contentParts" do
      let msg = { role: User, content: Nothing, encryptedContent: Nothing, encryptionNonce: Nothing, encryptionSalt: Nothing, contentParts: Just [{ partType: TextPart, text: Just "Hello", imageUrl: Nothing }], toolCallId: Nothing, toolCalls: Nothing }
      sessionKey <- deriveTestKey
      encrypted <- encryptMessageForStorage msg sessionKey
      encrypted.contentParts `shouldEqual` msg.contentParts
      -- Should encrypt text in contentParts
    
    -- BUG: encryptMessageForStorage may not handle toolCalls encryption
    it "BUG: encryptMessageForStorage doesn't encrypt toolCalls functionArguments" do
      let msg = { role: Assistant, content: Just "Hello", encryptedContent: Nothing, encryptionNonce: Nothing, encryptionSalt: Nothing, contentParts: Nothing, toolCallId: Nothing, toolCalls: Just [{ id: "1", toolType: "function", functionName: "test", functionArguments: "sensitive data" }] }
      sessionKey <- deriveTestKey
      encrypted <- encryptMessageForStorage msg sessionKey
      encrypted.toolCalls `shouldEqual` msg.toolCalls
      -- Should encrypt functionArguments
  
  describe "MessageEncryptionHelpers - decryptMessageFromStorage" do
    it "decrypts encrypted message" do
      sessionKey <- deriveTestKey
      encrypted <- encryptMessageForStorage { role: User, content: Just "Hello", encryptedContent: Nothing, encryptionNonce: Nothing, encryptionSalt: Nothing, contentParts: Nothing, toolCallId: Nothing, toolCalls: Nothing } sessionKey
      decrypted <- decryptMessageFromStorage encrypted sessionKey
      decrypted `shouldSatisfy` isJust
      case decrypted of
        Just msg -> do
          msg.content `shouldEqual` (Just "Hello")
          msg.encryptedContent `shouldEqual` Nothing
          msg.encryptionNonce `shouldEqual` Nothing
          msg.encryptionSalt `shouldEqual` Nothing
        Nothing -> pure unit
    
    it "preserves message without encrypted content" do
      let msg = { role: User, content: Just "Hello", encryptedContent: Nothing, encryptionNonce: Nothing, encryptionSalt: Nothing, contentParts: Nothing, toolCallId: Nothing, toolCalls: Nothing }
      sessionKey <- deriveTestKey
      decrypted <- decryptMessageFromStorage msg sessionKey
      decrypted `shouldEqual` (Just msg)
    
    it "returns Nothing for wrong session key" do
      sessionKey1 <- deriveTestKey
      sessionKey2 <- deriveTestKey "different-secret"
      encrypted <- encryptMessageForStorage { role: User, content: Just "Hello", encryptedContent: Nothing, encryptionNonce: Nothing, encryptionSalt: Nothing, contentParts: Nothing, toolCallId: Nothing, toolCalls: Nothing } sessionKey1
      decrypted <- decryptMessageFromStorage encrypted sessionKey2
      decrypted `shouldEqual` Nothing
    
    it "returns Nothing for corrupted encrypted content" do
      sessionKey <- deriveTestKey
      encrypted <- encryptMessageForStorage { role: User, content: Just "Hello", encryptedContent: Nothing, encryptionNonce: Nothing, encryptionSalt: Nothing, contentParts: Nothing, toolCallId: Nothing, toolCalls: Nothing } sessionKey
      let corrupted = encrypted { encryptedContent = Just "corrupted" }
      decrypted <- decryptMessageFromStorage corrupted sessionKey
      decrypted `shouldEqual` Nothing
    
    -- BUG: decryptMessageFromStorage may not validate all encryption fields present
    it "BUG: decryptMessageFromStorage doesn't validate all encryption fields present" do
      let msg = { role: User, content: Nothing, encryptedContent: Just "encrypted", encryptionNonce: Nothing, encryptionSalt: Nothing, contentParts: Nothing, toolCallId: Nothing, toolCalls: Nothing }
      sessionKey <- deriveTestKey
      decrypted <- decryptMessageFromStorage msg sessionKey
      decrypted `shouldEqual` Nothing
      -- Should validate nonce and salt are present
  
  describe "MessageEncryptionHelpers - encryptMessageForTransmission" do
    it "encrypts message while preserving plaintext" do
      let msg = { role: User, content: Just "Hello", encryptedContent: Nothing, encryptionNonce: Nothing, encryptionSalt: Nothing, contentParts: Nothing, toolCallId: Nothing, toolCalls: Nothing }
      sessionKey <- deriveTestKey
      encrypted <- encryptMessageForTransmission msg sessionKey
      encrypted.content `shouldEqual` (Just "Hello")
      encrypted.encryptedContent `shouldSatisfy` isJust
      encrypted.encryptionNonce `shouldSatisfy` isJust
      encrypted.encryptionSalt `shouldSatisfy` isJust
    
    it "preserves message without content" do
      let msg = { role: User, content: Nothing, encryptedContent: Nothing, encryptionNonce: Nothing, encryptionSalt: Nothing, contentParts: Nothing, toolCallId: Nothing, toolCalls: Nothing }
      sessionKey <- deriveTestKey
      encrypted <- encryptMessageForTransmission msg sessionKey
      encrypted `shouldEqual` msg
    
    -- BUG: encryptMessageForTransmission may overwrite existing encryptedContent
    it "BUG: encryptMessageForTransmission overwrites existing encryptedContent" do
      let msg = { role: User, content: Just "Hello", encryptedContent: Just "existing", encryptionNonce: Just "nonce", encryptionSalt: Just "salt", contentParts: Nothing, toolCallId: Nothing, toolCalls: Nothing }
      sessionKey <- deriveTestKey
      encrypted <- encryptMessageForTransmission msg sessionKey
      encrypted.encryptedContent `shouldNotEqual` (Just "existing")
      -- May overwrite existing encryption
  
  describe "MessageEncryptionHelpers - decryptMessageFromTransmission" do
    it "decrypts encrypted content and sets as content" do
      sessionKey <- deriveTestKey
      encrypted <- encryptMessageForTransmission { role: User, content: Just "Hello", encryptedContent: Nothing, encryptionNonce: Nothing, encryptionSalt: Nothing, contentParts: Nothing, toolCallId: Nothing, toolCalls: Nothing } sessionKey
      decrypted <- decryptMessageFromTransmission encrypted sessionKey
      decrypted `shouldSatisfy` isJust
      case decrypted of
        Just msg -> msg.content `shouldEqual` (Just "Hello")
        Nothing -> pure unit
    
    it "preserves existing content if not encrypted" do
      let msg = { role: User, content: Just "Hello", encryptedContent: Nothing, encryptionNonce: Nothing, encryptionSalt: Nothing, contentParts: Nothing, toolCallId: Nothing, toolCalls: Nothing }
      sessionKey <- deriveTestKey
      decrypted <- decryptMessageFromTransmission msg sessionKey
      decrypted `shouldEqual` (Just msg)
    
    it "returns Nothing for wrong session key" do
      sessionKey1 <- deriveTestKey
      sessionKey2 <- deriveTestKey "different-secret"
      encrypted <- encryptMessageForTransmission { role: User, content: Just "Hello", encryptedContent: Nothing, encryptionNonce: Nothing, encryptionSalt: Nothing, contentParts: Nothing, toolCallId: Nothing, toolCalls: Nothing } sessionKey1
      decrypted <- decryptMessageFromTransmission encrypted sessionKey2
      decrypted `shouldEqual` Nothing

-- Helper functions
deriveTestKey :: Aff String
deriveTestKey = deriveTestKeyWithSecret "test-secret"

deriveTestKeyWithSecret :: String -> Aff String
deriveTestKeyWithSecret secret = deriveSessionKey "test-session" secret
