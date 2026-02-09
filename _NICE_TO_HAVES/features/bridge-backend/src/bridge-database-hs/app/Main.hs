-- | Bridge Database CLI
-- | Command-line interface for database operations
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
module Main where

import Bridge.Database (openDatabase, getSnapshotFFI, listSnapshotsFFI, deleteSnapshotFFI, getSessionsBySessionIdFFI, recordBalanceHistoryFFI, getBalanceHistoryFFI, saveSnapshotFFI, saveSessionFFI)
import Bridge.Database.Schema (Snapshot(..))
import Bridge.Database.Operations
import Data.Aeson (encode, decode, ToJSON, FromJSON)
import Data.Aeson.Types (Value)
import GHC.Generics (Generic)
import qualified Data.ByteString.Lazy as BL
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.IO as TIO
import System.Environment (getArgs)
import System.IO (hPutStrLn, stderr, stdin, hGetContents)
import System.Exit (exitFailure)

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

-- | Global database handle (simplified - would use proper state management)
type DatabaseHandle = FilePath

-- | Main entry point
main :: IO ()
main = do
  args <- getArgs
  case args of
    ["open", dbPath] -> do
      handle <- openDatabase dbPath
      -- Output handle as JSON (simplified - just path for now)
      putStrLn (encode dbPath)
    
    ["save-snapshot", dbPath, input] -> do
      case decode (BL.fromStrict (TE.encodeUtf8 (T.pack input))) :: Maybe SnapshotData of
        Just snapshotData -> do
          handle <- openDatabase dbPath
          -- Convert SnapshotData to Snapshot and save
          -- Parse timestamp and create Snapshot
          -- Use saveSnapshotFFI which handles timestamp parsing internally
          saveSnapshotFFI handle 
            (T.pack (sdId snapshotData))
            (T.pack (sdTimestamp snapshotData))
            (T.pack (sdStateHash snapshotData))
            (T.pack (sdData snapshotData))
            (fmap T.pack (sdTrigger snapshotData))
            (fmap T.pack (sdDescription snapshotData))
          putStrLn (sdId snapshotData)
        Nothing -> do
          hPutStrLn stderr "Invalid snapshot data"
          exitFailure
    
    ["get-snapshot", dbPath, id] -> do
      handle <- openDatabase dbPath
      result <- getSnapshotFFI handle (T.pack id)
      case result of
        Just snapshot -> putStrLn (encode snapshot)
        Nothing -> putStrLn "null"
    
    ["list-snapshots", dbPath, limit, offset] -> do
      handle <- openDatabase dbPath
      let limitVal = read limit :: Int
      let offsetVal = read offset :: Int
      snapshots <- listSnapshotsFFI handle (Just limitVal) (Just offsetVal)
      putStrLn (encode snapshots)
    
    ["delete-snapshot", dbPath, id] -> do
      handle <- openDatabase dbPath
      result <- deleteSnapshotFFI handle (T.pack id)
      putStrLn (if result then "true" else "false")
    
    ["save-session", dbPath, input] -> do
      case decode (BL.fromStrict (TE.encodeUtf8 (T.pack input))) :: Maybe SessionData of
        Just sessionData -> do
          handle <- openDatabase dbPath
          -- Convert SessionData to SessionRecord and save
          -- Save session (saveSessionFFI handles timestamp parsing internally)
          saveSessionFFI handle
            (T.pack (sessId sessionData))
            (T.pack (sessSessionId sessionData))
            (sessPromptTokens sessionData)
            (sessCompletionTokens sessionData)
            (sessTotalTokens sessionData)
            (sessCost sessionData)
            (T.pack (sessModel sessionData))
            (T.pack (sessProvider sessionData))
            (T.pack (sessStartedAt sessionData))
            (fmap T.pack (sessEndedAt sessionData))
          putStrLn (sessId sessionData)
        Nothing -> do
          hPutStrLn stderr "Invalid session data"
          exitFailure
    
    ["get-sessions", dbPath, sessionId] -> do
      handle <- openDatabase dbPath
      sessions <- getSessionsBySessionIdFFI handle (T.pack sessionId)
      putStrLn (encode sessions)
    
    ["record-balance", dbPath, input] -> do
      case decode (BL.fromStrict (TE.encodeUtf8 (T.pack input))) :: Maybe BalanceHistoryData of
        Just balanceData -> do
          handle <- openDatabase dbPath
          id <- recordBalanceHistoryFFI handle 
            (bhdDiem balanceData) 
            (bhdUsd balanceData) 
            (bhdEffective balanceData) 
            (bhdConsumptionRate balanceData) 
            (bhdTimeToDepletion balanceData)
          putStrLn (T.unpack id)
        Nothing -> do
          hPutStrLn stderr "Invalid balance data"
          exitFailure
    
    ["get-balance-history", dbPath, limit, offset] -> do
      handle <- openDatabase dbPath
      let limitVal = read limit :: Int
      let offsetVal = read offset :: Int
      history <- getBalanceHistoryFFI handle (Just limitVal) (Just offsetVal)
      putStrLn (encode history)
    
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
