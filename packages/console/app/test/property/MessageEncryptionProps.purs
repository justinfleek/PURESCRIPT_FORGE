-- | Message Encryption Property Tests
-- | Property-based tests for encryption invariants
-- |
-- | **Purpose:** Tests cryptographic properties and invariants
-- | **Coverage:** All encryption properties, roundtrip correctness, key derivation
module Test.Property.MessageEncryptionProps where

import Prelude

import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual, shouldNotEqual)
import Data.Maybe (Maybe(..), isJust)
import Effect.Aff (Aff)
import Console.App.Routes.Omega.Util.MessageEncryption
  ( EncryptedMessage
  , encryptMessage
  , decryptMessage
  , deriveSessionKey
  )

spec :: Spec Unit
spec = do
  describe "MessageEncryption Properties" do
    it "prop_encrypt_decrypt_roundtrip: encrypt then decrypt returns original" do
      sessionKey <- deriveSessionKey "test-session" "test-secret"
      let original = "Test message"
      encrypted <- encryptMessage original sessionKey
      decrypted <- decryptMessage encrypted sessionKey
      decrypted `shouldEqual` (Just original)
    
    it "prop_encrypt_deterministic_nonce: same plaintext produces different ciphertexts" do
      sessionKey <- deriveSessionKey "test-session" "test-secret"
      encrypted1 <- encryptMessage "Same message" sessionKey
      encrypted2 <- encryptMessage "Same message" sessionKey
      encrypted1.encryptedContent `shouldNotEqual` encrypted2.encryptedContent
      encrypted1.nonce `shouldNotEqual` encrypted2.nonce
    
    it "prop_decrypt_wrong_key_fails: decrypting with wrong key returns Nothing" do
      sessionKey1 <- deriveSessionKey "test-session" "test-secret-1"
      sessionKey2 <- deriveSessionKey "test-session" "test-secret-2"
      encrypted <- encryptMessage "Test message" sessionKey1
      decrypted <- decryptMessage encrypted sessionKey2
      decrypted `shouldEqual` Nothing
    
    it "prop_derive_key_deterministic: same inputs produce same key" do
      key1 <- deriveSessionKey "session-1" "secret-1"
      key2 <- deriveSessionKey "session-1" "secret-1"
      key1 `shouldEqual` key2
    
    it "prop_derive_key_different_sessions: different sessions produce different keys" do
      key1 <- deriveSessionKey "session-1" "secret"
      key2 <- deriveSessionKey "session-2" "secret"
      key1 `shouldNotEqual` key2
    
    it "prop_derive_key_different_secrets: different secrets produce different keys" do
      key1 <- deriveSessionKey "session" "secret-1"
      key2 <- deriveSessionKey "session" "secret-2"
      key1 `shouldNotEqual` key2
    
    it "prop_encrypt_empty_string: empty string encrypts and decrypts correctly" do
      sessionKey <- deriveSessionKey "test-session" "test-secret"
      encrypted <- encryptMessage "" sessionKey
      decrypted <- decryptMessage encrypted sessionKey
      decrypted `shouldEqual` (Just "")
    
    it "prop_encrypt_unicode: Unicode characters encrypt and decrypt correctly" do
      sessionKey <- deriveSessionKey "test-session" "test-secret"
      let unicode = "Hello 世界 🌍"
      encrypted <- encryptMessage unicode sessionKey
      decrypted <- decryptMessage encrypted sessionKey
      decrypted `shouldEqual` (Just unicode)
    
    it "prop_encrypt_large_message: large messages encrypt and decrypt correctly" do
      sessionKey <- deriveSessionKey "test-session" "test-secret"
      let largeMessage = String.joinWith "" $ replicate 10000 "A"
      encrypted <- encryptMessage largeMessage sessionKey
      decrypted <- decryptMessage encrypted sessionKey
      decrypted `shouldEqual` (Just largeMessage)
    
    it "prop_encrypt_modify_ciphertext: modifying ciphertext causes decryption to fail" do
      sessionKey <- deriveSessionKey "test-session" "test-secret"
      encrypted <- encryptMessage "Test" sessionKey
      let modified = encrypted { encryptedContent = encrypted.encryptedContent <> "X" }
      decrypted <- decryptMessage modified sessionKey
      decrypted `shouldEqual` Nothing
    
    it "prop_encrypt_modify_nonce: modifying nonce causes decryption to fail" do
      sessionKey <- deriveSessionKey "test-session" "test-secret"
      encrypted <- encryptMessage "Test" sessionKey
      let modified = encrypted { nonce = encrypted.nonce <> "X" }
      decrypted <- decryptMessage modified sessionKey
      decrypted `shouldEqual` Nothing
    
    it "prop_encrypt_modify_salt: modifying salt causes decryption to fail" do
      sessionKey <- deriveSessionKey "test-session" "test-secret"
      encrypted <- encryptMessage "Test" sessionKey
      let modified = encrypted { salt = encrypted.salt <> "X" }
      decrypted <- decryptMessage modified sessionKey
      decrypted `shouldEqual` Nothing

-- Helper function
replicate :: Int -> String -> String
replicate n s = if n <= 0 then "" else s <> replicate (n - 1) s
