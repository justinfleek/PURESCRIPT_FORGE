{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

-- | Bridge Security Secrets Manager
-- |
-- | Secure secrets management with encryption at rest,
-- | key rotation, and SQLite-backed persistence.
-- | Uses AES-256-GCM encryption via Bridge.Auth.Encryption.
-- |
-- | Dependencies:
-- | - Bridge.Auth.Encryption: AES-256-GCM encryption/decryption
-- | - Control.Concurrent.STM: Thread-safe cache
-- | - Database.SQLite.Simple: Persistent storage
-- | - Data.UUID: Secret record IDs
module Bridge.Security.Secrets where

import Bridge.Auth.Encryption
  ( encryptApiKey
  , decryptApiKey
  , EncryptionResult(..)
  , MasterSecret
  )
import Control.Concurrent.STM
  ( TVar
  , newTVarIO
  , readTVarIO
  , atomically
  , readTVar
  , writeTVar
  )
import Database.SQLite.Simple
  ( Connection
  , open
  , close
  , execute_
  , execute
  , query
  , Only(..)
  )
import Database.SQLite.Simple.FromRow (FromRow(..), field)
import Database.SQLite.Simple.ToRow (ToRow(..), toRow)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import Data.Time (UTCTime, getCurrentTime)
import Data.UUID (UUID)
import Data.UUID.V4 (nextRandom)
import qualified Data.UUID as UUID

-- | Secret metadata (non-sensitive information about a secret)
data SecretMetadata = SecretMetadata
  { smName :: Text
  , smDescription :: Text
  , smCreatedAt :: UTCTime
  , smUpdatedAt :: UTCTime
  , smVersion :: Int
  }
  deriving (Eq, Show)

-- | Secret record (stored in database)
data SecretRecord = SecretRecord
  { srId :: Text
  , srName :: Text
  , srDescription :: Text
  , srEncryptedValue :: Text
  , srNonce :: Text
  , srSalt :: Text
  , srVersion :: Int
  , srCreatedAt :: UTCTime
  , srUpdatedAt :: UTCTime
  }
  deriving (Eq, Show)

instance FromRow SecretRecord where
  fromRow = SecretRecord
    <$> field <*> field <*> field
    <*> field <*> field <*> field
    <*> field <*> field <*> field

instance ToRow SecretRecord where
  toRow sr = toRow
    ( srId sr, srName sr, srDescription sr
    , srEncryptedValue sr, srNonce sr, srSalt sr
    , srVersion sr, srCreatedAt sr, srUpdatedAt sr
    )

-- | Secrets manager
data SecretsManager = SecretsManager
  { smDbPath :: FilePath
  , smMasterSecret :: MasterSecret
  , smCache :: TVar (Map Text Text) -- name -> decrypted value cache
  }

-- | Create secrets manager
-- |
-- | Opens the SQLite database, creates the secrets table if needed,
-- | and initializes an empty in-memory cache.
createSecretsManager :: FilePath -> MasterSecret -> IO SecretsManager
createSecretsManager dbPath masterSecret = do
  conn <- open dbPath
  initSecretsSchema conn
  close conn

  cache <- newTVarIO Map.empty
  pure SecretsManager
    { smDbPath = dbPath
    , smMasterSecret = masterSecret
    , smCache = cache
    }

-- | Initialize secrets schema
initSecretsSchema :: Connection -> IO ()
initSecretsSchema conn = do
  execute_ conn "CREATE TABLE IF NOT EXISTS secrets (\
    \id TEXT PRIMARY KEY,\
    \name TEXT NOT NULL UNIQUE,\
    \description TEXT NOT NULL DEFAULT '',\
    \encrypted_value TEXT NOT NULL,\
    \nonce TEXT NOT NULL,\
    \salt TEXT NOT NULL,\
    \version INTEGER NOT NULL DEFAULT 1,\
    \created_at TEXT NOT NULL,\
    \updated_at TEXT NOT NULL\
    \)"
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_secrets_name ON secrets(name)"
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_secrets_updated_at ON secrets(updated_at)"

-- | Store a secret
-- |
-- | Encrypts the value and stores it in the database.
-- | If a secret with the same name exists, it is overwritten
-- | with an incremented version.
storeSecret :: SecretsManager -> Text -> Text -> Text -> IO (Either String Text)
storeSecret manager name description value = do
  encResult <- encryptApiKey value (smMasterSecret manager)
  case encResult of
    Left err -> pure (Left ("Encryption failed: " ++ err))
    Right encrypted -> do
      now <- getCurrentTime
      secretId <- UUID.toText <$> nextRandom

      conn <- open (smDbPath manager)

      -- Check for existing secret
      existing <- query conn
        "SELECT version FROM secrets WHERE name = ?"
        (Only name) :: IO [Only Int]

      let version = case existing of
            (Only v : _) -> v + 1
            [] -> 1

      -- Delete existing if present
      execute conn "DELETE FROM secrets WHERE name = ?" (Only name)

      -- Insert new version
      let record = SecretRecord
            { srId = secretId
            , srName = name
            , srDescription = description
            , srEncryptedValue = encryptedData encrypted
            , srNonce = nonce encrypted
            , srSalt = salt encrypted
            , srVersion = version
            , srCreatedAt = now
            , srUpdatedAt = now
            }

      execute conn
        "INSERT INTO secrets (id, name, description, encrypted_value, nonce, salt, version, created_at, updated_at) \
        \VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)"
        record

      close conn

      -- Update cache
      atomically $ do
        cache <- readTVar (smCache manager)
        writeTVar (smCache manager) (Map.insert name value cache)

      pure (Right secretId)

-- | Get a secret by name
-- |
-- | First checks the in-memory cache, then falls back to
-- | database lookup with decryption.
getSecret :: SecretsManager -> Text -> IO (Either String Text)
getSecret manager name = do
  -- Check cache first
  cache <- readTVarIO (smCache manager)
  case Map.lookup name cache of
    Just value -> pure (Right value)
    Nothing -> do
      conn <- open (smDbPath manager)
      results <- query conn
        "SELECT id, name, description, encrypted_value, nonce, salt, version, created_at, updated_at \
        \FROM secrets WHERE name = ?"
        (Only name) :: IO [SecretRecord]
      close conn

      case results of
        [] -> pure (Left ("Secret not found: " ++ T.unpack name))
        (record : _) -> do
          let encrypted = EncryptionResult
                { encryptedData = srEncryptedValue record
                , nonce = srNonce record
                , salt = srSalt record
                }
          decResult <- decryptApiKey encrypted (smMasterSecret manager)
          case decResult of
            Left err -> pure (Left ("Decryption failed: " ++ err))
            Right value -> do
              -- Update cache
              atomically $ do
                c <- readTVar (smCache manager)
                writeTVar (smCache manager) (Map.insert name value c)
              pure (Right value)

-- | Rotate a secret
-- |
-- | Re-encrypts the secret with a new value.
-- | Increments the version number.
rotateSecret :: SecretsManager -> Text -> Text -> IO (Either String Text)
rotateSecret manager name newValue = do
  -- Get existing metadata
  conn <- open (smDbPath manager)
  results <- query conn
    "SELECT description FROM secrets WHERE name = ?"
    (Only name) :: IO [Only Text]
  close conn

  case results of
    [] -> pure (Left ("Secret not found: " ++ T.unpack name))
    (Only description : _) ->
      storeSecret manager name description newValue

-- | List all secrets (metadata only, no decrypted values)
-- |
-- | Returns metadata for all stored secrets.
listSecrets :: SecretsManager -> IO [SecretMetadata]
listSecrets manager = do
  conn <- open (smDbPath manager)
  results <- query conn
    "SELECT name, description, created_at, updated_at, version \
    \FROM secrets ORDER BY name ASC"
    () :: IO [(Text, Text, UTCTime, UTCTime, Int)]
  close conn

  pure (map (\(name, desc, created, updated, ver) ->
    SecretMetadata
      { smName = name
      , smDescription = desc
      , smCreatedAt = created
      , smUpdatedAt = updated
      , smVersion = ver
      }) results)

-- | Delete a secret
-- |
-- | Removes the secret from the database and cache.
-- | Returns True if the secret was found and deleted.
deleteSecret :: SecretsManager -> Text -> IO Bool
deleteSecret manager name = do
  conn <- open (smDbPath manager)
  execute conn "DELETE FROM secrets WHERE name = ?" (Only name)

  -- Check if anything was deleted by querying
  results <- query conn
    "SELECT COUNT(*) FROM secrets WHERE name = ?"
    (Only name) :: IO [Only Int]
  close conn

  -- Remove from cache
  atomically $ do
    cache <- readTVar (smCache manager)
    writeTVar (smCache manager) (Map.delete name cache)

  case results of
    (Only 0 : _) -> pure True
    _ -> pure False
