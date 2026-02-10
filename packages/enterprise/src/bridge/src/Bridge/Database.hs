-- | Bridge Database FFI Facade
-- |
-- | Top-level database module providing JSON-based FFI wrappers
-- | around the SQLite storage layer. All FFI functions accept
-- | and return Text (JSON strings) for Bridge server interop.
-- |
-- | Dependencies:
-- | - Database.SQLite.Simple: SQLite connection
-- | - Bridge.Database.Schema: Schema initialization
-- | - Bridge.Database.Operations: CRUD operations
-- | - Data.Aeson: JSON encoding/decoding
-- | - Data.Time: UTC time parsing
module Bridge.Database
  ( DatabaseHandle(..)
  , openDatabase
  , closeDatabase
  , saveSnapshotFFI
  , getSnapshotFFI
  , listSnapshotsFFI
  , deleteSnapshotFFI
  , saveSessionFFI
  , getSessionsBySessionIdFFI
  , recordBalanceHistoryFFI
  , getBalanceHistoryFFI
  , parseUTCTime
  ) where

import Database.SQLite.Simple (Connection, open, close)
import Bridge.Database.Schema
  ( Snapshot(..)
  , SessionRecord(..)
  , BalanceHistoryRecord(..)
  , initializeSchema
  )
import Bridge.Database.Operations
  ( saveSnapshot
  , getSnapshot
  , listSnapshots
  , deleteSnapshot
  , saveSession
  , getSessionsBySessionId
  , recordBalanceHistory
  , getBalanceHistory
  )
import Data.Aeson (encode, decode, ToJSON, FromJSON, object, (.=))
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Encoding as TLE
import qualified Data.ByteString.Lazy as BL
import Data.Time (UTCTime)
import Data.Time.Format (parseTimeM, defaultTimeLocale)

-- | Database handle (opaque wrapper around SQLite Connection)
newtype DatabaseHandle = DatabaseHandle
  { dbConnection :: Connection
  }

-- | Open database
-- |
-- | Opens a SQLite connection and initializes the schema.
openDatabase :: FilePath -> IO DatabaseHandle
openDatabase dbPath = do
  conn <- open dbPath
  initializeSchema conn
  pure (DatabaseHandle conn)

-- | Close database
closeDatabase :: DatabaseHandle -> IO ()
closeDatabase (DatabaseHandle conn) = close conn

-- | Helper: encode result to JSON Text
toJsonText :: ToJSON a => a -> Text
toJsonText = TL.toStrict . TLE.decodeUtf8 . encode

-- | Helper: decode JSON Text
fromJsonText :: FromJSON a => Text -> Maybe a
fromJsonText = decode . TLE.encodeUtf8 . TL.fromStrict

-- | Helper: parse UTC time from ISO 8601 string
-- |
-- | Tries 3 common formats:
-- | 1. "%Y-%m-%dT%H:%M:%S%QZ" (full ISO with Z)
-- | 2. "%Y-%m-%dT%H:%M:%S%Q" (ISO without Z)
-- | 3. "%Y-%m-%d %H:%M:%S" (space-separated)
parseUTCTime :: Text -> Maybe UTCTime
parseUTCTime txt =
  let s = T.unpack txt
  in case parseTimeM True defaultTimeLocale "%Y-%m-%dT%H:%M:%S%QZ" s of
    Just t -> Just t
    Nothing -> case parseTimeM True defaultTimeLocale "%Y-%m-%dT%H:%M:%S%Q" s of
      Just t -> Just t
      Nothing -> parseTimeM True defaultTimeLocale "%Y-%m-%d %H:%M:%S" s

-- | Save snapshot (FFI wrapper)
-- |
-- | Accepts JSON Text containing a Snapshot record.
-- | Returns the snapshot ID as Text.
saveSnapshotFFI :: DatabaseHandle -> Text -> IO Text
saveSnapshotFFI (DatabaseHandle conn) jsonText =
  case fromJsonText jsonText of
    Just snapshot -> saveSnapshot conn snapshot
    Nothing -> pure "error: invalid snapshot JSON"

-- | Get snapshot by ID (FFI wrapper)
-- |
-- | Returns JSON Text of the snapshot, or "null" if not found.
getSnapshotFFI :: DatabaseHandle -> Text -> IO Text
getSnapshotFFI (DatabaseHandle conn) snapshotId = do
  result <- getSnapshot conn snapshotId
  case result of
    Just snapshot -> pure (toJsonText snapshot)
    Nothing -> pure "null"

-- | List snapshots (FFI wrapper)
-- |
-- | Accepts optional limit and offset as Ints.
-- | Returns JSON array Text of snapshots.
listSnapshotsFFI :: DatabaseHandle -> Maybe Int -> Maybe Int -> IO Text
listSnapshotsFFI (DatabaseHandle conn) limit offset = do
  snapshots <- listSnapshots conn limit offset
  pure (toJsonText snapshots)

-- | Delete snapshot (FFI wrapper)
-- |
-- | Returns "true" if deleted, "false" if not found.
deleteSnapshotFFI :: DatabaseHandle -> Text -> IO Text
deleteSnapshotFFI (DatabaseHandle conn) snapshotId = do
  deleted <- deleteSnapshot conn snapshotId
  if deleted
    then pure "true"
    else pure "false"

-- | Save session (FFI wrapper)
-- |
-- | Accepts JSON Text containing a SessionRecord.
-- | Returns the session record ID as Text.
saveSessionFFI :: DatabaseHandle -> Text -> IO Text
saveSessionFFI (DatabaseHandle conn) jsonText =
  case fromJsonText jsonText of
    Just session -> saveSession conn session
    Nothing -> pure "error: invalid session JSON"

-- | Get sessions by session ID (FFI wrapper)
-- |
-- | Returns JSON array Text of session records.
getSessionsBySessionIdFFI :: DatabaseHandle -> Text -> IO Text
getSessionsBySessionIdFFI (DatabaseHandle conn) sessionId = do
  sessions <- getSessionsBySessionId conn sessionId
  pure (toJsonText sessions)

-- | Record balance history (FFI wrapper)
-- |
-- | Accepts individual balance values.
-- | Returns the balance history record ID as Text.
recordBalanceHistoryFFI :: DatabaseHandle -> Double -> Double -> Double -> Double -> Maybe Int -> IO Text
recordBalanceHistoryFFI (DatabaseHandle conn) diem usd effective consumptionRate timeToDepletion =
  recordBalanceHistory conn diem usd effective consumptionRate timeToDepletion

-- | Get balance history (FFI wrapper)
-- |
-- | Returns JSON array Text of balance history records.
getBalanceHistoryFFI :: DatabaseHandle -> Maybe Int -> Maybe Int -> IO Text
getBalanceHistoryFFI (DatabaseHandle conn) limit offset = do
  history <- getBalanceHistory conn limit offset
  pure (toJsonText history)
