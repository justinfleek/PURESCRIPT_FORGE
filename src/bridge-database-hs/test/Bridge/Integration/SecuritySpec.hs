{-# LANGUAGE OverloadedStrings #-}

-- | Security Integration Tests - End-to-End Security Flow Tests
-- |
-- | **What:** Integration tests for security workflows (encryption, secrets management,
-- |         input validation). Tests complete security flows end-to-end.
-- | **Why:** Ensures security mechanisms work correctly together. Validates security
-- |         properties hold in practice.
-- | **How:** Tests encryption/decryption, secret storage/retrieval, input validation
-- |         with real dependencies.
module Bridge.Integration.SecuritySpec where

import Test.Hspec
import Bridge.Auth.Encryption
import Bridge.Security.Secrets
import qualified Data.Text as T
import System.Environment (setEnv, unsetEnv)

-- | Test encryption and decryption flow
testEncryptionFlow :: Spec
testEncryptionFlow = describe "Encryption Flow" $ do
  it "encrypts and decrypts API key correctly" $ do
    -- Set master secret
    setEnv "BRIDGE_ENCRYPTION_KEY" "test-master-secret-key-12345"
    
    -- Get master secret
    masterSecretResult <- getMasterSecret
    masterSecret <- case masterSecretResult of
      Right ms -> pure ms
      Left err -> expectationFailure ("Failed to get master secret: " ++ err)
    
    -- Encrypt API key
    apiKey <- pure ("sk-test-api-key-12345" :: ApiKey)
    encryptionResult <- encryptApiKey apiKey masterSecret
    
    case encryptionResult of
      Right encrypted -> do
        -- Decrypt API key
        decryptionResult <- decryptApiKey encrypted masterSecret
        case decryptionResult of
          Right decrypted -> do
            decrypted `shouldBe` apiKey
          Left err -> expectationFailure ("Decryption failed: " ++ err)
      Left err -> expectationFailure ("Encryption failed: " ++ err)
    
    -- Cleanup
    unsetEnv "BRIDGE_ENCRYPTION_KEY"

-- | Test secrets management flow
testSecretsManagementFlow :: Spec
testSecretsManagementFlow = describe "Secrets Management Flow" $ do
  it "stores and retrieves secrets correctly" $ do
    -- Set master secret
    setEnv "BRIDGE_ENCRYPTION_KEY" "test-master-secret-key-12345"
    
    -- Create secrets manager
    managerResult <- createSecretsManager "./test-secrets.db"
    manager <- case managerResult of
      Right m -> pure m
      Left err -> expectationFailure ("Failed to create secrets manager: " ++ err)
    
    -- Store secret
    secretName <- pure ("test_api_key" :: T.Text)
    secretValue <- pure ("sk-test-secret-value-12345" :: T.Text)
    storeResult <- storeSecret secretName secretValue manager
    
    case storeResult of
      Right _ -> do
        -- Retrieve secret
        getResult <- getSecret secretName manager
        case getResult of
          Right retrieved -> do
            retrieved `shouldBe` secretValue
          Left err -> expectationFailure ("Failed to retrieve secret: " ++ err)
      Left err -> expectationFailure ("Failed to store secret: " ++ err)
    
    -- Cleanup
    unsetEnv "BRIDGE_ENCRYPTION_KEY"
    removeFile "./test-secrets.db"
  where
    import System.Directory (removeFile)

-- | Test secret rotation flow
testSecretRotationFlow :: Spec
testSecretRotationFlow = describe "Secret Rotation Flow" $ do
  it "rotates secrets correctly" $ do
    -- Set master secret
    setEnv "BRIDGE_ENCRYPTION_KEY" "test-master-secret-key-12345"
    
    -- Create secrets manager
    managerResult <- createSecretsManager "./test-secrets-rotation.db"
    manager <- case managerResult of
      Right m -> pure m
      Left err -> expectationFailure ("Failed to create secrets manager: " ++ err)
    
    -- Store initial secret
    secretName <- pure ("rotatable_secret" :: T.Text)
    initialValue <- pure ("sk-initial-value" :: T.Text)
    storeResult1 <- storeSecret secretName initialValue manager
    
    case storeResult1 of
      Right _ -> do
        -- Rotate secret
        newValue <- pure ("sk-new-value-12345" :: T.Text)
        rotateResult <- rotateSecret secretName newValue manager
        
        case rotateResult of
          Right _ -> do
            -- Verify new secret is active
            getResult <- getSecret secretName manager
            case getResult of
              Right retrieved -> do
                retrieved `shouldBe` newValue
              Left err -> expectationFailure ("Failed to retrieve rotated secret: " ++ err)
          Left err -> expectationFailure ("Failed to rotate secret: " ++ err)
      Left err -> expectationFailure ("Failed to store initial secret: " ++ err)
    
    -- Cleanup
    unsetEnv "BRIDGE_ENCRYPTION_KEY"
    removeFile "./test-secrets-rotation.db"
  where
    import System.Directory (removeFile)

-- | Integration test suite
spec :: Spec
spec = do
  testEncryptionFlow
  testSecretsManagementFlow
  testSecretRotationFlow
