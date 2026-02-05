-- | Message Encryption - End-to-End Encryption for Total Privacy
-- |
-- | **Purpose:** Provides AES-256-GCM encryption for message content
-- |         ensuring messages are never stored or transmitted in plaintext.
-- | **Security:** Uses AES-256-GCM authenticated encryption with per-message nonces.
-- |         Keys derived from session/user secrets using PBKDF2.
-- |
-- | **Encryption Flow:**
-- | 1. Client encrypts message content before sending
-- | 2. Server stores encrypted content (never sees plaintext)
-- | 3. Server decrypts only for processing (in-memory only)
-- | 4. Server re-encrypts before storage
-- | 5. Client decrypts when retrieving messages
-- |
-- | **Key Management:**
-- | - Per-session encryption keys derived from session ID + user secret
-- | - Keys never stored, only derived on-demand
-- | - Each message uses unique nonce for security
module Console.App.Routes.Omega.Util.MessageEncryption
  ( EncryptedMessage
  , encryptMessage
  , decryptMessage
  , deriveSessionKey
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)

-- | Encrypted message structure
-- | Contains encrypted content, nonce, and salt for key derivation
-- | All binary data is hex-encoded for storage and transmission
type EncryptedMessage =
  { encryptedContent :: String  -- Binary data as hex string (ciphertext + auth tag)
  , nonce :: String  -- Binary data as hex string (12 bytes = 24 hex chars)
  , salt :: String  -- Binary data as hex string (16 bytes = 32 hex chars)
  }

-- | Encrypt message content
-- | Uses AES-256-GCM with authenticated encryption
-- | Returns encrypted message with nonce and salt
encryptMessage :: String -> String -> Aff EncryptedMessage
encryptMessage plaintext sessionKey = encryptMessageImpl plaintext sessionKey

foreign import encryptMessageImpl :: String -> String -> Aff EncryptedMessage

-- | Decrypt message content
-- | Verifies authentication tag before decryption
-- | Returns plaintext or Nothing if decryption fails
decryptMessage :: EncryptedMessage -> String -> Aff (Maybe String)
decryptMessage encrypted sessionKey = decryptMessageImpl encrypted sessionKey

foreign import decryptMessageImpl :: EncryptedMessage -> String -> Aff (Maybe String)

-- | Derive session encryption key from session ID and user secret
-- | Uses PBKDF2 key derivation for secure key generation
-- | Returns hex-encoded encryption key
deriveSessionKey :: String -> String -> Aff String
deriveSessionKey sessionId userSecret = deriveSessionKeyImpl sessionId userSecret

foreign import deriveSessionKeyImpl :: String -> String -> Aff String
