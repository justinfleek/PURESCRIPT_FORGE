{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

-- | API Key Encryption - Encryption at Rest for API Keys
-- |
-- | **What:** Provides encryption/decryption for API keys stored at rest.
-- |         Uses AES-256-GCM encryption with key derivation from master secret.
-- | **Why:** API keys are sensitive credentials that must be encrypted when stored.
-- |         Prevents key theft if storage is compromised.
-- | **How:** Encrypts API keys using AES-256-GCM with authenticated encryption.
-- |         Uses PBKDF2 for key derivation. Master key from environment variable.
-- |
-- | **Dependencies:**
-- | - `cryptonite`: Cryptography library
-- | - `memory`: Secure memory handling
-- |
-- | **Mathematical Foundation:**
-- | - **Encryption:** `ciphertext = AES-256-GCM(plaintext, key, nonce)`
-- | - **Key Derivation:** `key = PBKDF2(masterSecret, salt, iterations)`
-- | - **Authenticated Encryption:** GCM provides both confidentiality and authenticity
-- |
-- | **Security Properties:**
-- | - Keys encrypted with AES-256-GCM
-- | - Master key never stored (environment variable only)
-- | - Nonce generated randomly for each encryption
-- | - Authenticated encryption prevents tampering
-- |
-- | **Usage Example:**
-- | ```haskell
-- | import Bridge.Auth.Encryption as Encryption
-- |
-- | -- Encrypt API key
-- | encrypted <- Encryption.encryptApiKey "sk-..." masterSecret
-- |
-- | -- Decrypt API key
-- | decrypted <- Encryption.decryptApiKey encrypted masterSecret
-- | ```
module Bridge.Auth.Encryption where

import qualified Crypto.Cipher.AES as AES
import qualified Crypto.Cipher.Types as Cipher
import qualified Crypto.Error as CryptoError
import qualified Crypto.KDF.PBKDF2 as PBKDF2
import qualified Crypto.Random as Random
import qualified Data.ByteString as BS
import qualified Data.ByteString.Base64 as Base64
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import Data.Maybe (Maybe(..), fromMaybe)
import Control.Exception (try, SomeException)

-- | Encryption result
data EncryptionResult = EncryptionResult
  { encryptedData :: T.Text -- Base64-encoded ciphertext
  , nonce :: T.Text -- Base64-encoded nonce
  , salt :: T.Text -- Base64-encoded salt
  }
  deriving (Eq, Show)

-- | Master secret (from environment)
type MasterSecret = T.Text

-- | API key plaintext
type ApiKey = T.Text

-- | PBKDF2 iterations (should be high for security)
pbkdf2Iterations :: Int
pbkdf2Iterations = 100000

-- | AES key size (256 bits = 32 bytes)
aesKeySize :: Int
aesKeySize = 32

-- | GCM nonce size (96 bits = 12 bytes)
gcmNonceSize :: Int
gcmNonceSize = 12

-- | Salt size (128 bits = 16 bytes)
saltSize :: Int
saltSize = 16

-- | Encrypt API key
-- |
-- | **Purpose:** Encrypts API key using AES-256-GCM with key derivation.
-- | **Parameters:**
-- | - `apiKey`: Plaintext API key
-- | - `masterSecret`: Master encryption key (from environment)
-- | **Returns:** Either error or encrypted result
-- |
-- | **Process:**
-- | 1. Generate random salt and nonce
-- | 2. Derive encryption key from master secret + salt
-- | 3. Encrypt API key with AES-256-GCM
-- | 4. Return encrypted data, nonce, and salt (all Base64-encoded)
encryptApiKey :: ApiKey -> MasterSecret -> IO (Either String EncryptionResult)
encryptApiKey apiKey masterSecret = do
    -- Generate random salt and nonce
    saltBytes <- Random.getRandomBytes saltSize
    nonceBytes <- Random.getRandomBytes gcmNonceSize
    
    -- Derive encryption key
    let masterSecretBytes = TE.encodeUtf8 masterSecret
    let derivedKey = PBKDF2.generate (PBKDF2.Parameters PBKDF2.SHA256 pbkdf2Iterations aesKeySize) masterSecretBytes saltBytes
    
    -- Initialize AES cipher
    case CryptoError.eitherCryptoError (AES.initAES derivedKey) of
      Left err -> pure (Left ("AES initialization failed: " ++ show err))
      Right cipher -> do
        -- Encrypt with GCM
        let apiKeyBytes = TE.encodeUtf8 apiKey
        let (ciphertext, authTag) = Cipher.aeadEncrypt Cipher.AEAD_GCM cipher nonceBytes [] apiKeyBytes
        
        -- Combine ciphertext and auth tag
        let encryptedBytes = BS.append ciphertext authTag
        
        -- Base64 encode
        let encryptedB64 = Base64.encode encryptedBytes
        let nonceB64 = Base64.encode nonceBytes
        let saltB64 = Base64.encode saltBytes
        
        pure (Right EncryptionResult
          { encryptedData = TE.decodeUtf8 encryptedB64
          , nonce = TE.decodeUtf8 nonceB64
          , salt = TE.decodeUtf8 saltB64
          })

-- | Decrypt API key
-- |
-- | **Purpose:** Decrypts API key using stored encrypted data, nonce, and salt.
-- | **Parameters:**
-- | - `encrypted`: Encryption result (from encryptApiKey)
-- | - `masterSecret`: Master encryption key (from environment)
-- | **Returns:** Either error or decrypted API key
-- |
-- | **Process:**
-- | 1. Decode Base64-encoded data
-- | 2. Derive encryption key from master secret + salt
-- | 3. Decrypt with AES-256-GCM
-- | 4. Return plaintext API key
decryptApiKey :: EncryptionResult -> MasterSecret -> IO (Either String ApiKey)
decryptApiKey encrypted masterSecret = do
  -- Decode Base64
  encryptedBytesResult <- case Base64.decode (TE.encodeUtf8 encrypted.encryptedData) of
    Right bytes -> pure (Right bytes)
    Left err -> pure (Left ("Base64 decode error: " ++ show err))
  
  case encryptedBytesResult of
    Left err -> pure (Left err)
    Right encryptedBytes -> do
      nonceBytesResult <- case Base64.decode (TE.encodeUtf8 encrypted.nonce) of
        Right bytes -> pure (Right bytes)
        Left err -> pure (Left ("Base64 decode nonce error: " ++ show err))
      
      case nonceBytesResult of
        Left err -> pure (Left err)
        Right nonceBytes -> do
          saltBytesResult <- case Base64.decode (TE.encodeUtf8 encrypted.salt) of
            Right bytes -> pure (Right bytes)
            Left err -> pure (Left ("Base64 decode salt error: " ++ show err))
          
          case saltBytesResult of
            Left err -> pure (Left err)
            Right saltBytes -> do
              -- Derive encryption key (same as encryption)
              let masterSecretBytes = TE.encodeUtf8 masterSecret
              let derivedKey = PBKDF2.generate (PBKDF2.Parameters PBKDF2.SHA256 pbkdf2Iterations aesKeySize) masterSecretBytes saltBytes
              
              -- Initialize AES cipher
              case CryptoError.eitherCryptoError (AES.initAES derivedKey) of
                Left err -> pure (Left ("AES initialization failed: " ++ show err))
                Right cipher -> do
                  -- Split ciphertext and auth tag (last 16 bytes)
                  let (ciphertext, authTag) = BS.splitAt (BS.length encryptedBytes - 16) encryptedBytes
                  
                  -- Decrypt with GCM
                  case Cipher.aeadDecrypt Cipher.AEAD_GCM cipher nonceBytes [] ciphertext authTag of
                    Just plaintext -> pure (Right (TE.decodeUtf8 plaintext))
                    Nothing -> pure (Left "Decryption failed: authentication tag mismatch")

-- | Get master secret from environment
-- |
-- | **Purpose:** Retrieves master encryption key from environment variable.
-- | **Returns:** Either error or master secret
-- |
-- | **Security:** Master secret must be set via environment variable, never hardcoded.
getMasterSecret :: IO (Either String MasterSecret)
getMasterSecret = do
  secret <- System.Environment.lookupEnv "BRIDGE_ENCRYPTION_KEY"
  case secret of
    Just s -> pure (Right (T.pack s))
    Nothing -> pure (Left "BRIDGE_ENCRYPTION_KEY environment variable not set")
  where
    import qualified System.Environment
