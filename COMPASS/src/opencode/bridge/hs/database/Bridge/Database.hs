-- | Database Module
-- | Main database interface for Bridge Server
{-# LANGUAGE ForeignFunctionInterface #-}
module Bridge.Database where

import Database.SQLite.Simple
import Bridge.Database.Schema
import Bridge.Database.Operations
import Data.Text (Text)
import Data.Time.Clock (UTCTime)
import Data.Time.Format (parseTimeM, defaultTimeLocale, iso8601DateFormat)
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE

-- | Database handle (opaque type for FFI)
data DatabaseHandle = DatabaseHandle Connection

-- | Open database
openDatabase :: FilePath -> IO DatabaseHandle
openDatabase path = do
  conn <- open path
  initializeSchema conn
  return (DatabaseHandle conn)

-- | Close database
closeDatabase :: DatabaseHandle -> IO ()
closeDatabase (DatabaseHandle conn) = close conn

-- | Save snapshot (FFI-friendly)
saveSnapshotFFI :: DatabaseHandle -> Text -> Text -> Text -> Text -> Maybe Text -> Maybe Text -> IO Text
saveSnapshotFFI (DatabaseHandle conn) id timestamp stateHash data trigger description = do
  -- Parse timestamp from ISO string
  timestamp' <- parseUTCTime timestamp
  let snapshot = Snapshot id timestamp' stateHash data trigger description
  saveSnapshot conn snapshot

-- | Get snapshot (FFI-friendly) - returns JSON string
getSnapshotFFI :: DatabaseHandle -> Text -> IO (Maybe Snapshot)
getSnapshotFFI (DatabaseHandle conn) = getSnapshot conn

-- | List snapshots (FFI-friendly)
listSnapshotsFFI :: DatabaseHandle -> Maybe Int -> Maybe Int -> IO [Snapshot]
listSnapshotsFFI (DatabaseHandle conn) = listSnapshots conn

-- | Delete snapshot (FFI-friendly)
deleteSnapshotFFI :: DatabaseHandle -> Text -> IO Bool
deleteSnapshotFFI (DatabaseHandle conn) = deleteSnapshot conn

-- | Save session (FFI-friendly)
saveSessionFFI :: DatabaseHandle -> Text -> Text -> Int -> Int -> Int -> Double -> Text -> Text -> Text -> Maybe Text -> IO Text
saveSessionFFI (DatabaseHandle conn) id sessionId promptTokens completionTokens totalTokens cost model provider startedAt endedAt = do
  startedAt' <- parseUTCTime startedAt
  endedAt' <- case endedAt of
    Just e -> Just <$> parseUTCTime e
    Nothing -> return Nothing
  let session = SessionRecord id sessionId promptTokens completionTokens totalTokens cost model provider startedAt' endedAt'
  saveSession conn session

-- | Get sessions by session ID (FFI-friendly)
getSessionsBySessionIdFFI :: DatabaseHandle -> Text -> IO [SessionRecord]
getSessionsBySessionIdFFI (DatabaseHandle conn) = getSessionsBySessionId conn

-- | Record balance history (FFI-friendly)
recordBalanceHistoryFFI :: DatabaseHandle -> Double -> Double -> Double -> Double -> Maybe Int -> IO Text
recordBalanceHistoryFFI (DatabaseHandle conn) = recordBalanceHistory conn

-- | Get balance history (FFI-friendly)
getBalanceHistoryFFI :: DatabaseHandle -> Maybe Int -> Maybe Int -> IO [BalanceHistoryRecord]
getBalanceHistoryFFI (DatabaseHandle conn) = getBalanceHistory conn

-- | Parse UTCTime from ISO string
parseUTCTime :: Text -> IO UTCTime
parseUTCTime t = do
  let formats = 
        [ "%Y-%m-%dT%H:%M:%S%QZ"
        , "%Y-%m-%dT%H:%M:%SZ"
        , "%Y-%m-%d %H:%M:%S"
        ]
  let parsed = foldl (\acc fmt -> case acc of
        Just _ -> acc
        Nothing -> parseTimeM True defaultTimeLocale fmt (T.unpack t)
        ) Nothing formats
  case parsed of
    Just time -> return time
    Nothing -> error ("Failed to parse timestamp: " ++ T.unpack t)
