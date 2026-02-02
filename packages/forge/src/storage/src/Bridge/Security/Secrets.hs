{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

-- | Secrets Management - Secure Secret Storage and Rotation
-- |
-- | **What:** Provides secure storage and rotation for secrets (API keys, encryption keys,
-- |         database passwords). Uses encrypted storage with master key encryption.
-- | **Why:** Secrets must be stored securely and rotated regularly. Prevents secret
-- |         leakage and enables key rotation without service downtime.
-- | **How:** Stores secrets encrypted with master key. Supports secret rotation with
-- |         versioning. Provides secure secret retrieval.
-- |
-- | **Dependencies:**
-- | - `Bridge.Auth.Encryption`: Encryption utilities
-- | - `Database.SQLite.Simple`: Secret storage
-- |
-- | **Mathematical Foundation:**
-- | - **Secret Storage:** `encryptedSecret = AES-256-GCM(secret, masterKey)`
-- | - **Secret Rotation:** New version encrypted, old version retained for rollback
-- | - **Secret Retrieval:** Decrypt with master key, return plaintext
-- |
-- | **Usage Example:**
-- | ```haskell
-- | import Bridge.Security.Secrets as Secrets
-- |
-- | -- Store secret
-- | Secrets.storeSecret "api_key" "sk-..." manager
-- |
-- | -- Retrieve secret
-- | secret <- Secrets.getSecret "api_key" manager
-- |
-- | -- Rotate secret
-- | Secrets.rotateSecret "api_key" "sk-new-..." manager
-- | ```
module Bridge.Security.Secrets where

import Prelude hiding (read)
import Control.Concurrent.STM (TVar, newTVarIO, readTVar, writeTVar, atomically)
import Database.SQLite.Simple (Connection, open, close, execute, query, query_, Only(..), FromRow(..), field)
import qualified Data.Text as T
import qualified Data.ByteString as BS
import Data.Time (UTCTime, getCurrentTime)
import Data.UUID (UUID)
import Data.UUID.V4 (nextRandom)
import qualified Data.UUID as UUID
import Bridge.Auth.Encryption (MasterSecret, EncryptionResult(..), encryptApiKey, decryptApiKey, getMasterSecret)
import qualified Data.Map.Strict as Map
import Control.Exception (try, SomeException)
import Data.Time.Format (formatTime, defaultTimeLocale, parseTimeM)

-- | Secret metadata
data SecretMetadata = SecretMetadata
  { smName :: T.Text
  , smVersion :: Int
  , smCreatedAt :: UTCTime
  , smUpdatedAt :: UTCTime
  , smIsActive :: Bool
  }
  deriving (Eq, Show)

-- | Encrypted secret record
data SecretRecord = SecretRecord
  { srId :: T.Text
  , srName :: T.Text
  , srVersion :: Int
  , srEncryptedData :: EncryptionResult
  , srCreatedAt :: UTCTime
  , srUpdatedAt :: UTCTime
  , srIsActive :: Bool
  }
  deriving (Eq, Show)

-- | Secrets manager
data SecretsManager = SecretsManager
  { smDbPath :: FilePath
  , smMasterSecret :: MasterSecret
  , smCache :: TVar (Map.Map T.Text SecretRecord) -- In-memory cache
  }

-- | Create secrets manager
-- |
-- | **Purpose:** Creates a secrets manager instance.
-- | **Parameters:**
-- | - `dbPath`: Path to secrets database
-- | **Returns:** Either error or secrets manager
createSecretsManager :: FilePath -> IO (Either String SecretsManager)
createSecretsManager dbPath = do
  -- Get master secret from environment
  masterSecretResult <- getMasterSecret
  case masterSecretResult of
    Left err -> pure (Left ("Failed to get master secret: " ++ err))
    Right masterSecret -> do
      result <- try $ do
    
    -- Initialize database
    conn <- open dbPath
    execute conn
      "CREATE TABLE IF NOT EXISTS secrets (id TEXT PRIMARY KEY, name TEXT, version INTEGER, encrypted_data TEXT, nonce TEXT, salt TEXT, created_at TEXT, updated_at TEXT, is_active INTEGER)"
      ()
    close conn
    
    -- Create cache
    cache <- newTVarIO Map.empty
    
        pure SecretsManager
          { smDbPath = dbPath
          , smMasterSecret = masterSecret
          , smCache = cache
          }
        
        case result of
          Right value -> pure (Right value)
          Left err -> pure (Left ("Create secrets manager failed: " ++ show (err :: SomeException)))

-- | Store secret
-- |
-- | **Purpose:** Stores a secret encrypted in the database.
-- | **Parameters:**
-- | - `name`: Secret name (e.g., "venice_api_key")
-- | - `value`: Plaintext secret value
-- | - `manager`: Secrets manager
-- | **Returns:** Either error or success
storeSecret :: T.Text -> T.Text -> SecretsManager -> IO (Either String ())
storeSecret name value manager = do
  -- Encrypt secret
  encryptionResult <- encryptApiKey value (smMasterSecret manager)
  case encryptionResult of
    Left err -> pure (Left ("Encryption failed: " ++ err))
    Right encrypted -> do
      result <- try $ do
        -- Get current version
        currentVersion <- getCurrentVersion name manager
        
        -- Create secret record
        now <- getCurrentTime
        secretId <- UUID.toText <$> nextRandom
        
        let newVersion = currentVersion + 1
        let record = SecretRecord
              { srId = secretId
              , srName = name
              , srVersion = newVersion
              , srEncryptedData = encrypted
              , srCreatedAt = now
              , srUpdatedAt = now
              , srIsActive = True
              }
        
        -- Store in database
        conn <- open (smDbPath manager)
        execute conn
          "INSERT INTO secrets (id, name, version, encrypted_data, nonce, salt, created_at, updated_at, is_active) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)"
          (srId record, srName record, srVersion record, encryptedData encrypted, nonce encrypted, salt encrypted, T.pack (formatTimeStr (srCreatedAt record)), T.pack (formatTimeStr (srUpdatedAt record)), 1 :: Int)
        close conn
        where
          formatTimeStr :: UTCTime -> String
          formatTimeStr t = formatTime defaultTimeLocale "%Y-%m-%d %H:%M:%S" t
        
        -- Update cache
        atomically $ do
          cache <- readTVar (smCache manager)
          writeTVar (smCache manager) (Map.insert name record cache)
        
        pure ()
  
  case result of
    Right _ -> pure (Right ())
    Left err -> pure (Left ("Store secret failed: " ++ show (err :: SomeException)))
  where
    import Control.Concurrent.STM (atomically, readTVar, writeTVar)
    import qualified Data.Map.Strict as Map
    
    getCurrentVersion :: T.Text -> SecretsManager -> IO Int
    getCurrentVersion secretName mgr = do
      conn <- open (smDbPath mgr)
      results <- query conn
        "SELECT MAX(version) FROM secrets WHERE name = ? AND is_active = 1"
        (Only secretName)
      close conn
      case results of
        [] -> pure 0
        (Only (Just v):_) -> pure v
        (Only Nothing:_) -> pure 0
        _ -> pure 0

-- | Get secret
-- |
-- | **Purpose:** Retrieves and decrypts a secret.
-- | **Parameters:**
-- | - `name`: Secret name
-- | - `manager`: Secrets manager
-- | **Returns:** Either error or plaintext secret
getSecret :: T.Text -> SecretsManager -> IO (Either String T.Text)
getSecret name manager = do
  -- Check cache first
  cached <- atomically $ do
    cache <- readTVar (smCache manager)
    pure (Map.lookup name cache)
  
  recordResult <- case cached of
    Just r -> pure (Right r)
    Nothing -> do
      -- Load from database
      result <- try $ do
        conn <- open (smDbPath manager)
        results <- query conn
          "SELECT id, name, version, encrypted_data, nonce, salt, created_at, updated_at, is_active FROM secrets WHERE name = ? AND is_active = 1 ORDER BY version DESC LIMIT 1"
          (Only name) :: IO [(T.Text, T.Text, Int, T.Text, T.Text, T.Text, T.Text, T.Text, Int)]
        close conn
        pure results
      
      case result of
        Left err -> pure (Left ("Database query failed: " ++ show (err :: SomeException)))
        Right [] -> pure (Left ("Secret not found: " ++ T.unpack name))
        Right (r:_) -> do
          let (id, nameVal, version, encryptedData, nonce, salt, createdAt, updatedAt, isActive) = r
          createdTimeResult <- parseTime (T.unpack createdAt)
          updatedTimeResult <- parseTime (T.unpack updatedAt)
          case (createdTimeResult, updatedTimeResult) of
            (Left err, _) -> pure (Left err)
            (_, Left err) -> pure (Left err)
            (Right createdTime, Right updatedTime) -> do
              let record = SecretRecord
                    { srId = id
                    , srName = nameVal
                    , srVersion = version
                    , srEncryptedData = EncryptionResult
                        { encryptedData = encryptedData
                        , nonce = nonce
                        , salt = salt
                        }
                    , srCreatedAt = createdTime
                    , srUpdatedAt = updatedTime
                    , srIsActive = isActive == 1
                    }
              -- Update cache
              atomically $ do
                cache <- readTVar (smCache manager)
                writeTVar (smCache manager) (Map.insert name record cache)
              pure (Right record)
      where
        parseTime :: String -> IO (Either String UTCTime)
        parseTime s = case parseTimeM True defaultTimeLocale "%Y-%m-%d %H:%M:%S" s of
          Just t -> pure (Right t)
          Nothing -> pure (Left ("Invalid time format: " ++ s))
  
  case recordResult of
    Left err -> pure (Left err)
    Right record -> do
      -- Decrypt secret
      decryptionResult <- decryptApiKey (srEncryptedData record) (smMasterSecret manager)
      case decryptionResult of
        Left err -> pure (Left ("Decryption failed: " ++ err))
        Right plaintext -> pure (Right plaintext)
  where
    import Control.Concurrent.STM (atomically, readTVar, writeTVar)
    import qualified Data.Map.Strict as Map

-- | Rotate secret
-- |
-- | **Purpose:** Rotates a secret by creating a new version and deactivating old versions.
-- | **Parameters:**
-- | - `name`: Secret name
-- | - `newValue`: New secret value
-- | - `manager`: Secrets manager
-- | **Returns:** Either error or success
rotateSecret :: T.Text -> T.Text -> SecretsManager -> IO (Either String ())
rotateSecret name newValue manager = do
  -- Deactivate old versions
  deactivateResult <- try $ do
    conn <- open (smDbPath manager)
    execute conn
      "UPDATE secrets SET is_active = 0 WHERE name = ? AND is_active = 1"
      (Only name)
    close conn
  
  case deactivateResult of
    Left err -> pure (Left ("Deactivate old versions failed: " ++ show (err :: SomeException)))
    Right _ -> do
      -- Store new version
      storeResult <- storeSecret name newValue manager
      case storeResult of
        Left err -> pure (Left err)
        Right _ -> pure (Right ())

-- | List secrets
-- |
-- | **Purpose:** Lists all secret names.
-- | **Parameters:**
-- | - `manager`: Secrets manager
-- | **Returns:** List of secret names
listSecrets :: SecretsManager -> IO [T.Text]
listSecrets manager = do
  conn <- open (smDbPath manager)
  results <- query_ conn "SELECT DISTINCT name FROM secrets WHERE is_active = 1"
  close conn
  pure (map (\(Only name) -> name) results)

-- | Delete secret
-- |
-- | **Purpose:** Deletes a secret (deactivates all versions).
-- | **Parameters:**
-- | - `name`: Secret name
-- | - `manager`: Secrets manager
-- | **Returns:** Either error or success
deleteSecret :: T.Text -> SecretsManager -> IO (Either String ())
deleteSecret name manager = do
  result <- try $ do
    conn <- open (smDbPath manager)
    execute conn
      "UPDATE secrets SET is_active = 0 WHERE name = ?"
      (Only name)
    close conn
    
    -- Remove from cache
    atomically $ do
      cache <- readTVar (smCache manager)
      writeTVar (smCache manager) (Map.delete name cache)
    
    pure ()
  
  case result of
    Right _ -> pure (Right ())
    Left err -> pure (Left ("Delete secret failed: " ++ show (err :: SomeException)))
  where
    import Control.Concurrent.STM (atomically, readTVar, writeTVar)
    import qualified Data.Map.Strict as Map
