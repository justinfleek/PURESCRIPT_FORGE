{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

-- | API Key Encryption - Encryption at Rest for API Keys
-- |
-- | Uses AES-256-GCM encryption with key derivation from master secret.
-- | Master key from environment variable (never hardcoded).
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
import qualified System.Environment as Env
import Control.Exception (try, SomeException)

-- | Encryption result
data EncryptionResult = EncryptionResult
  { encryptedData :: T.Text
  , nonce :: T.Text
  , salt :: T.Text
  }
  deriving (Eq, Show)

-- | Master secret (from environment)
type MasterSecret = T.Text

-- | API key plaintext
type ApiKey = T.Text

-- | PBKDF2 iterations
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

-- | Encrypt API key using AES-256-GCM with key derivation
encryptApiKey :: ApiKey -> MasterSecret -> IO (Either String EncryptionResult)
encryptApiKey apiKey masterSecret = do
    saltBytes <- Random.getRandomBytes saltSize
    nonceBytes <- Random.getRandomBytes gcmNonceSize

    let masterSecretBytes = TE.encodeUtf8 masterSecret
    let derivedKey = PBKDF2.generate
          (PBKDF2.prfHMAC PBKDF2.SHA256)
          (PBKDF2.Parameters pbkdf2Iterations aesKeySize)
          masterSecretBytes
          saltBytes

    case CryptoError.eitherCryptoError (AES.initAES derivedKey) of
      Left err -> pure (Left ("AES initialization failed: " ++ show err))
      Right cipher -> do
        let apiKeyBytes = TE.encodeUtf8 apiKey
        let (ciphertext, authTag) = Cipher.aeadEncrypt Cipher.AEAD_GCM cipher nonceBytes [] apiKeyBytes

        let encryptedBytes = BS.append ciphertext authTag

        let encryptedB64 = Base64.encode encryptedBytes
        let nonceB64 = Base64.encode nonceBytes
        let saltB64 = Base64.encode saltBytes

        pure (Right EncryptionResult
          { encryptedData = TE.decodeUtf8 encryptedB64
          , nonce = TE.decodeUtf8 nonceB64
          , salt = TE.decodeUtf8 saltB64
          })

-- | Decrypt API key using stored encrypted data, nonce, and salt
decryptApiKey :: EncryptionResult -> MasterSecret -> IO (Either String ApiKey)
decryptApiKey encrypted masterSecret = do
  case Base64.decode (TE.encodeUtf8 (encryptedData encrypted)) of
    Left err -> pure (Left ("Base64 decode error: " ++ show err))
    Right encryptedBytes ->
      case Base64.decode (TE.encodeUtf8 (nonce encrypted)) of
        Left err -> pure (Left ("Base64 decode nonce error: " ++ show err))
        Right nonceBytes ->
          case Base64.decode (TE.encodeUtf8 (salt encrypted)) of
            Left err -> pure (Left ("Base64 decode salt error: " ++ show err))
            Right saltBytes -> do
              let masterSecretBytes = TE.encodeUtf8 masterSecret
              let derivedKey = PBKDF2.generate
                    (PBKDF2.prfHMAC PBKDF2.SHA256)
                    (PBKDF2.Parameters pbkdf2Iterations aesKeySize)
                    masterSecretBytes
                    saltBytes

              case CryptoError.eitherCryptoError (AES.initAES derivedKey) of
                Left err -> pure (Left ("AES initialization failed: " ++ show err))
                Right cipher -> do
                  let (ciphertext, authTag) = BS.splitAt (BS.length encryptedBytes - 16) encryptedBytes

                  case Cipher.aeadDecrypt Cipher.AEAD_GCM cipher nonceBytes [] ciphertext authTag of
                    Just plaintext -> pure (Right (TE.decodeUtf8 plaintext))
                    Nothing -> pure (Left "Decryption failed: authentication tag mismatch")

-- | Get master secret from environment
getMasterSecret :: IO (Either String MasterSecret)
getMasterSecret = do
  secret <- Env.lookupEnv "BRIDGE_ENCRYPTION_KEY"
  case secret of
    Just s -> pure (Right (T.pack s))
    Nothing -> pure (Left "BRIDGE_ENCRYPTION_KEY environment variable not set")
