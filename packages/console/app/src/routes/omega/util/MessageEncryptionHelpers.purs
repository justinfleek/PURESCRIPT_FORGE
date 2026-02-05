-- | Message Encryption Helpers
-- | Provides transparent encryption/decryption for CommonMessage
-- |
-- | **Usage:**
-- | - encryptMessageForStorage: Encrypt message content before database storage
-- | - decryptMessageFromStorage: Decrypt message content after database retrieval
-- | - encryptMessageForTransmission: Encrypt message before sending to server
-- | - decryptMessageFromTransmission: Decrypt message after receiving from server
module Console.App.Routes.Omega.Util.MessageEncryptionHelpers
  ( encryptMessageForStorage
  , decryptMessageFromStorage
  , encryptMessageForTransmission
  , decryptMessageFromTransmission
  ) where

import Prelude

import Effect.Aff (Aff)
import Data.Maybe (Maybe(..), fromMaybe)
import Console.App.Routes.Omega.Util.Provider.Provider (CommonMessage)
import Console.App.Routes.Omega.Util.MessageEncryption
  ( EncryptedMessage
  , encryptMessage
  , decryptMessage
  , deriveSessionKey
  )

-- | Encrypt message content for database storage
-- | Moves plaintext content to encryptedContent field
-- | Returns message with encrypted content (plaintext removed)
encryptMessageForStorage :: CommonMessage -> String -> Aff CommonMessage
encryptMessageForStorage msg sessionKey = do
  case msg.content of
    Just plaintext -> do
      encrypted <- encryptMessage plaintext sessionKey
      pure msg
        { content = Nothing
        , encryptedContent = Just encrypted.encryptedContent
        , encryptionNonce = Just encrypted.nonce
        , encryptionSalt = Just encrypted.salt
        }
    Nothing -> pure msg  -- Already encrypted or no content

-- | Decrypt message content from database storage
-- | Moves encryptedContent to content field (plaintext)
-- | Returns message with decrypted content (encrypted fields cleared)
decryptMessageFromStorage :: CommonMessage -> String -> Aff (Maybe CommonMessage)
decryptMessageFromStorage msg sessionKey = do
  case msg.encryptedContent, msg.encryptionNonce, msg.encryptionSalt of
    Just encryptedContent, Just nonce, Just salt -> do
      let encrypted = { encryptedContent, nonce, salt }
      decrypted <- decryptMessage encrypted sessionKey
      case decrypted of
        Just plaintext -> pure $ Just msg
          { content = Just plaintext
          , encryptedContent = Nothing
          , encryptionNonce = Nothing
          , encryptionSalt = Nothing
          }
        Nothing -> pure Nothing  -- Decryption failed
    _, _, _ -> pure $ Just msg  -- Not encrypted or already decrypted

-- | Encrypt message for transmission to server
-- | Creates encrypted version while preserving plaintext for processing
encryptMessageForTransmission :: CommonMessage -> String -> Aff CommonMessage
encryptMessageForTransmission msg sessionKey = do
  case msg.content of
    Just plaintext -> do
      encrypted <- encryptMessage plaintext sessionKey
      pure msg
        { encryptedContent = Just encrypted.encryptedContent
        , encryptionNonce = Just encrypted.nonce
        , encryptionSalt = Just encrypted.salt
        }
    Nothing -> pure msg  -- No content to encrypt

-- | Decrypt message from transmission
-- | Decrypts encryptedContent and sets as content
decryptMessageFromTransmission :: CommonMessage -> String -> Aff (Maybe CommonMessage)
decryptMessageFromTransmission msg sessionKey = do
  case msg.encryptedContent, msg.encryptionNonce, msg.encryptionSalt of
    Just encryptedContent, Just nonce, Just salt -> do
      let encrypted = { encryptedContent, nonce, salt }
      decrypted <- decryptMessage encrypted sessionKey
      case decrypted of
        Just plaintext -> pure $ Just msg
          { content = Just plaintext
          }
        Nothing -> pure Nothing
    _, _, _ -> pure $ Just msg  -- Not encrypted
