{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

-- | Secrets Management - Secure Secret Storage and Rotation
-- |
-- | Provides secure storage and rotation for secrets (API keys, encryption keys,
-- | database passwords). Uses encrypted storage with master key encryption.
module Bridge.Security.Secrets
  ( SecretsManager
  , SecretMetadata(..)
  , createSecretsManager
  , storeSecret
  , getSecret
  , rotateSecret
  , listSecrets
  , deleteSecret
  ) where

import Prelude hiding (read)
import Control.Concurrent.STM (TVar, newTVarIO, readTVar, writeTVar, atomically)
import Database.SQLite.Simple (Connection, open, close, execute, query, query_, Only(..))
import qualified Data.Text as T
import Data.Text (Text)
import Data.Time (UTCTime, getCurrentTime)
import Data.UUID.V4 (nextRandom)
import qualified Data.UUID as UUID
import Bridge.Auth.Encryption (MasterSecret, EncryptionResult(..), encryptApiKey, decryptApiKey, getMasterSecret)
import qualified Data.Map.Strict as Map
import Control.Exception (try, SomeException)
import Data.Time.Format (formatTime, defaultTimeLocale, parseTimeM)

-- | Secret metadata
data SecretMetadata = SecretMetadata
  { smName :: Text
  , smVersion :: Int
  , smCreatedAt :: UTCTime
  , smUpdatedAt :: UTCTime
  , smIsActive :: Bool
  } deriving (Eq, Show)

-- | Encrypted secret record
data SecretRecord = SecretRecord
  { srId :: Text
  , srName :: Text
  , srVersion :: Int
  , srEncryptedData :: EncryptionResult
  , srCreatedAt :: UTCTime
  , srUpdatedAt :: UTCTime
  , srIsActive :: Bool
  } deriving (Eq, Show)

-- | Secrets manager
data SecretsManager = SecretsManager
  { smDbPath :: FilePath
  , smMasterSecret :: MasterSecret
  , smCache :: TVar (Map.Map Text SecretRecord)
  }

-- | Format time for database storage
formatTimeStr :: UTCTime -> String
formatTimeStr t = formatTime defaultTimeLocale "%Y-%m-%d %H:%M:%S" t

-- | Parse time from database
parseTime :: String -> IO (Either String UTCTime)
parseTime s = case parseTimeM True defaultTimeLocale "%Y-%m-%d %H:%M:%S" s of
  Just t -> pure (Right t)
  Nothing -> pure (Left ("Invalid time format: " ++ s))

-- | Create secrets manager
createSecretsManager :: FilePath -> IO (Either String SecretsManager)
createSecretsManager dbPath = do
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

-- | Get current version of a secret
getCurrentVersion :: Text -> SecretsManager -> IO Int
getCurrentVersion secretName mgr = do
  conn <- open (smDbPath mgr)
  results <- query conn
    "SELECT MAX(version) FROM secrets WHERE name = ? AND is_active = 1"
    (Only secretName) :: IO [Only (Maybe Int)]
  close conn
  case results of
    [] -> pure 0
    (Only (Just v):_) -> pure v
    (Only Nothing:_) -> pure 0

-- | Store secret
storeSecret :: Text -> Text -> SecretsManager -> IO (Either String ())
storeSecret name value manager = do
  encryptionResult <- encryptApiKey value (smMasterSecret manager)
  case encryptionResult of
    Left err -> pure (Left ("Encryption failed: " ++ err))
    Right encrypted -> do
      result <- try $ do
        currentVersion <- getCurrentVersion name manager
        
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
        
        conn <- open (smDbPath manager)
        execute conn
          "INSERT INTO secrets (id, name, version, encrypted_data, nonce, salt, created_at, updated_at, is_active) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)"
          ( srId record
          , srName record
          , srVersion record
          , encryptedData encrypted
          , nonce encrypted
          , salt encrypted
          , T.pack (formatTimeStr (srCreatedAt record))
          , T.pack (formatTimeStr (srUpdatedAt record))
          , (1 :: Int)
          )
        close conn
        
        atomically $ do
          cache <- readTVar (smCache manager)
          writeTVar (smCache manager) (Map.insert name record cache)
        
        pure ()
      
      case result of
        Right _ -> pure (Right ())
        Left err -> pure (Left ("Store secret failed: " ++ show (err :: SomeException)))

-- | Get secret
getSecret :: Text -> SecretsManager -> IO (Either String Text)
getSecret name manager = do
  cached <- atomically $ do
    cache <- readTVar (smCache manager)
    pure (Map.lookup name cache)
  
  recordResult <- case cached of
    Just r -> pure (Right r)
    Nothing -> do
      result <- try $ do
        conn <- open (smDbPath manager)
        results <- query conn
          "SELECT id, name, version, encrypted_data, nonce, salt, created_at, updated_at, is_active FROM secrets WHERE name = ? AND is_active = 1 ORDER BY version DESC LIMIT 1"
          (Only name) :: IO [(Text, Text, Int, Text, Text, Text, Text, Text, Int)]
        close conn
        pure results
      
      case result of
        Left err -> pure (Left ("Database query failed: " ++ show (err :: SomeException)))
        Right [] -> pure (Left ("Secret not found: " ++ T.unpack name))
        Right ((idVal, nameVal, version, encryptedDataVal, nonceVal, saltVal, createdAt, updatedAt, isActive):_) -> do
          createdTimeResult <- parseTime (T.unpack createdAt)
          updatedTimeResult <- parseTime (T.unpack updatedAt)
          case (createdTimeResult, updatedTimeResult) of
            (Left err, _) -> pure (Left err)
            (_, Left err) -> pure (Left err)
            (Right createdTime, Right updatedTime) -> do
              let record = SecretRecord
                    { srId = idVal
                    , srName = nameVal
                    , srVersion = version
                    , srEncryptedData = EncryptionResult
                        { encryptedData = encryptedDataVal
                        , nonce = nonceVal
                        , salt = saltVal
                        }
                    , srCreatedAt = createdTime
                    , srUpdatedAt = updatedTime
                    , srIsActive = isActive == 1
                    }
              atomically $ do
                cache <- readTVar (smCache manager)
                writeTVar (smCache manager) (Map.insert name record cache)
              pure (Right record)
  
  case recordResult of
    Left err -> pure (Left err)
    Right record -> do
      decryptionResult <- decryptApiKey (srEncryptedData record) (smMasterSecret manager)
      case decryptionResult of
        Left err -> pure (Left ("Decryption failed: " ++ err))
        Right plaintext -> pure (Right plaintext)

-- | Rotate secret
rotateSecret :: Text -> Text -> SecretsManager -> IO (Either String ())
rotateSecret name newValue manager = do
  deactivateResult <- try $ do
    conn <- open (smDbPath manager)
    execute conn
      "UPDATE secrets SET is_active = 0 WHERE name = ? AND is_active = 1"
      (Only name)
    close conn
  
  case deactivateResult of
    Left err -> pure (Left ("Deactivate old versions failed: " ++ show (err :: SomeException)))
    Right _ -> storeSecret name newValue manager

-- | List secrets
listSecrets :: SecretsManager -> IO [Text]
listSecrets manager = do
  conn <- open (smDbPath manager)
  results <- query_ conn "SELECT DISTINCT name FROM secrets WHERE is_active = 1" :: IO [Only Text]
  close conn
  pure (map (\(Only n) -> n) results)

-- | Delete secret
deleteSecret :: Text -> SecretsManager -> IO (Either String ())
deleteSecret name manager = do
  result <- try $ do
    conn <- open (smDbPath manager)
    execute conn
      "UPDATE secrets SET is_active = 0 WHERE name = ?"
      (Only name)
    close conn
    
    atomically $ do
      cache <- readTVar (smCache manager)
      writeTVar (smCache manager) (Map.delete name cache)
    
    pure ()
  
  case result of
    Right _ -> pure (Right ())
    Left err -> pure (Left ("Delete secret failed: " ++ show (err :: SomeException)))
