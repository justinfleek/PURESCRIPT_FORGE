-- | Bridge Database CLI
-- | Command-line interface for database operations
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
module Main where

import Bridge.Database.Schema (Snapshot(..))
import Bridge.Database.Operations
import Data.Aeson (encode, decode, ToJSON, FromJSON)
import GHC.Generics (Generic)
import qualified Data.ByteString.Lazy as BL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import System.Environment (getArgs)
import System.IO (hPutStrLn, stderr)
import System.Exit (exitFailure)
import Database.SQLite.Simple (open)

-- | Snapshot data (JSON-serializable)
data SnapshotData = SnapshotData
  { sdId :: String
  , sdTimestamp :: String
  , sdStateHash :: String
  , sdData :: String
  , sdTrigger :: Maybe String
  , sdDescription :: Maybe String
  }
  deriving (Show, Generic)

instance ToJSON SnapshotData
instance FromJSON SnapshotData

-- | Session data (JSON-serializable)
data SessionData = SessionData
  { sessId :: String
  , sessSessionId :: String
  , sessPromptTokens :: Int
  , sessCompletionTokens :: Int
  , sessTotalTokens :: Int
  , sessCost :: Double
  , sessModel :: String
  , sessProvider :: String
  , sessStartedAt :: String
  , sessEndedAt :: Maybe String
  }
  deriving (Show, Generic)

instance ToJSON SessionData
instance FromJSON SessionData

-- | Balance history data (JSON-serializable)
data BalanceHistoryData = BalanceHistoryData
  { bhdDiem :: Double
  , bhdUsd :: Double
  , bhdEffective :: Double
  , bhdConsumptionRate :: Double
  , bhdTimeToDepletion :: Maybe Int
  }
  deriving (Show, Generic)

instance ToJSON BalanceHistoryData
instance FromJSON BalanceHistoryData

-- | Main entry point
main :: IO ()
main = do
  args <- getArgs
  case args of
    ["open", dbPath] -> do
      conn <- open dbPath
      Bridge.Database.Schema.initializeSchema conn
      putStrLn (show (encode dbPath))

    ["save-snapshot", dbPath, input] -> do
      case decode (BL.fromStrict (TE.encodeUtf8 (T.pack input))) :: Maybe SnapshotData of
        Just snapshotData -> do
          conn <- open dbPath
          -- Save snapshot via operations module
          snapshotId' <- saveSnapshot conn (toSnapshot snapshotData)
          putStrLn (T.unpack snapshotId')
        Nothing -> do
          hPutStrLn stderr "Invalid snapshot data"
          exitFailure

    ["get-snapshot", dbPath, snapshotId'] -> do
      conn <- open dbPath
      result <- getSnapshot conn (T.pack snapshotId')
      case result of
        Just snapshot -> BL.putStr (encode snapshot)
        Nothing -> putStrLn "null"

    ["list-snapshots", dbPath, limit, offset] -> do
      conn <- open dbPath
      let limitVal = read limit :: Int
      let offsetVal = read offset :: Int
      snapshots <- listSnapshots conn (Just limitVal) (Just offsetVal)
      BL.putStr (encode snapshots)

    ["delete-snapshot", dbPath, snapshotId'] -> do
      conn <- open dbPath
      result <- deleteSnapshot conn (T.pack snapshotId')
      putStrLn (if result then "true" else "false")

    ["save-session", dbPath, input] -> do
      case decode (BL.fromStrict (TE.encodeUtf8 (T.pack input))) :: Maybe SessionData of
        Just sessionData -> do
          conn <- open dbPath
          sessionId' <- saveSession conn (toSessionRecord sessionData)
          putStrLn (T.unpack sessionId')
        Nothing -> do
          hPutStrLn stderr "Invalid session data"
          exitFailure

    ["get-sessions", dbPath, sessionId'] -> do
      conn <- open dbPath
      sessions <- getSessionsBySessionId conn (T.pack sessionId')
      BL.putStr (encode sessions)

    ["record-balance", dbPath, input] -> do
      case decode (BL.fromStrict (TE.encodeUtf8 (T.pack input))) :: Maybe BalanceHistoryData of
        Just balanceData -> do
          conn <- open dbPath
          balanceId <- recordBalanceHistory conn
            (bhdDiem balanceData)
            (bhdUsd balanceData)
            (bhdEffective balanceData)
            (bhdConsumptionRate balanceData)
            (bhdTimeToDepletion balanceData)
          putStrLn (T.unpack balanceId)
        Nothing -> do
          hPutStrLn stderr "Invalid balance data"
          exitFailure

    ["get-balance-history", dbPath, limit, offset] -> do
      conn <- open dbPath
      let limitVal = read limit :: Int
      let offsetVal = read offset :: Int
      history <- getBalanceHistory conn (Just limitVal) (Just offsetVal)
      BL.putStr (encode history)

    _ -> do
      hPutStrLn stderr "Usage: bridge-database <command> [args...]"
      hPutStrLn stderr "Commands:"
      hPutStrLn stderr "  open <path>"
      hPutStrLn stderr "  save-snapshot <path> <json>"
      hPutStrLn stderr "  get-snapshot <path> <id>"
      hPutStrLn stderr "  list-snapshots <path> <limit> <offset>"
      hPutStrLn stderr "  delete-snapshot <path> <id>"
      hPutStrLn stderr "  save-session <path> <json>"
      hPutStrLn stderr "  get-sessions <path> <sessionId>"
      hPutStrLn stderr "  record-balance <path> <json>"
      hPutStrLn stderr "  get-balance-history <path> <limit> <offset>"
      exitFailure

-- | Helper: Convert SnapshotData to Snapshot (placeholder timestamp)
toSnapshot :: SnapshotData -> Snapshot
toSnapshot sd = Snapshot
  { snapshotId = T.pack (sdId sd)
  , snapshotTimestamp = read (sdTimestamp sd)
  , snapshotStateHash = T.pack (sdStateHash sd)
  , snapshotData = T.pack (sdData sd)
  , snapshotTrigger = fmap T.pack (sdTrigger sd)
  , snapshotDescription = fmap T.pack (sdDescription sd)
  }

-- | Helper: Convert SessionData to SessionRecord (placeholder timestamp)
toSessionRecord :: SessionData -> SessionRecord
toSessionRecord sd = SessionRecord
  { sessionRecordId = T.pack (sessId sd)
  , sessionRecordSessionId = T.pack (sessSessionId sd)
  , sessionRecordPromptTokens = sessPromptTokens sd
  , sessionRecordCompletionTokens = sessCompletionTokens sd
  , sessionRecordTotalTokens = sessTotalTokens sd
  , sessionRecordCost = sessCost sd
  , sessionRecordModel = T.pack (sessModel sd)
  , sessionRecordProvider = T.pack (sessProvider sd)
  , sessionRecordStartedAt = read (sessStartedAt sd)
  , sessionRecordEndedAt = fmap read (sessEndedAt sd)
  }
