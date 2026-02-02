-- | Database Schema
-- | SQLite schema definitions for Bridge Server
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
module Bridge.Database.Schema where

import Database.SQLite.Simple
import Data.Text (Text)
import Data.Time (UTCTime)
import Data.Aeson (ToJSON, FromJSON)
import GHC.Generics (Generic)
import qualified Data.Text as T

-- | Snapshot record
data Snapshot = Snapshot
  { snapshotId :: Text
  , snapshotTimestamp :: UTCTime
  , snapshotStateHash :: Text
  , snapshotData :: Text -- JSON string
  , snapshotTrigger :: Maybe Text -- 'auto', 'manual', 'pre-edit'
  , snapshotDescription :: Maybe Text
  }
  deriving (Show, Eq, Generic)

instance ToJSON Snapshot
instance FromJSON Snapshot

-- | Session record
data SessionRecord = SessionRecord
  { sessionRecordId :: Text
  , sessionRecordSessionId :: Text
  , sessionRecordPromptTokens :: Int
  , sessionRecordCompletionTokens :: Int
  , sessionRecordTotalTokens :: Int
  , sessionRecordCost :: Double
  , sessionRecordModel :: Text
  , sessionRecordProvider :: Text
  , sessionRecordStartedAt :: UTCTime
  , sessionRecordEndedAt :: Maybe UTCTime
  }
  deriving (Show, Eq, Generic)

instance ToJSON SessionRecord
instance FromJSON SessionRecord

-- | Balance history record
data BalanceHistoryRecord = BalanceHistoryRecord
  { balanceHistoryId :: Text
  , balanceHistoryTimestamp :: UTCTime
  , balanceHistoryDiem :: Double
  , balanceHistoryUsd :: Double
  , balanceHistoryEffective :: Double
  , balanceHistoryConsumptionRate :: Double
  , balanceHistoryTimeToDepletion :: Maybe Int -- seconds
  }
  deriving (Show, Eq, Generic)

instance ToJSON BalanceHistoryRecord
instance FromJSON BalanceHistoryRecord

-- | Proof record
data ProofRecord = ProofRecord
  { proofId :: Text
  , proofTheoremName :: Text
  , proofFilePath :: Text
  , proofLineStart :: Int
  , proofLineEnd :: Int
  , proofStatement :: Text
  , proofText :: Text
  , proofStatus :: Text  -- 'proven', 'sorry', 'incomplete'
  , proofVerifiedAt :: UTCTime
  , proofVerifiedBy :: Maybe Text
  , proofDependencies :: Maybe Text  -- JSON array of theorem IDs
  , proofTags :: Maybe Text  -- JSON array of tags
  , proofDescription :: Maybe Text
  }
  deriving (Show, Eq, Generic)

instance ToJSON ProofRecord
instance FromJSON ProofRecord

-- | Initialize database schema
initializeSchema :: Connection -> IO ()
initializeSchema conn = do
  -- Snapshots table
  execute_ conn "CREATE TABLE IF NOT EXISTS snapshots (\
    \id TEXT PRIMARY KEY,\
    \timestamp TEXT NOT NULL,\
    \state_hash TEXT NOT NULL,\
    \data TEXT NOT NULL,\
    \trigger TEXT DEFAULT 'auto',\
    \description TEXT\
    \)"
  
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_snapshots_timestamp ON snapshots(timestamp)"
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_snapshots_state_hash ON snapshots(state_hash)"
  
  -- Sessions table
  execute_ conn "CREATE TABLE IF NOT EXISTS sessions (\
    \id TEXT PRIMARY KEY,\
    \session_id TEXT NOT NULL,\
    \prompt_tokens INTEGER NOT NULL,\
    \completion_tokens INTEGER NOT NULL,\
    \total_tokens INTEGER NOT NULL,\
    \cost REAL NOT NULL,\
    \model TEXT NOT NULL,\
    \provider TEXT NOT NULL,\
    \started_at TEXT NOT NULL,\
    \ended_at TEXT\
    \)"
  
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_sessions_session_id ON sessions(session_id)"
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_sessions_started_at ON sessions(started_at)"
  
  -- Balance history table
  execute_ conn "CREATE TABLE IF NOT EXISTS balance_history (\
    \id TEXT PRIMARY KEY,\
    \timestamp TEXT NOT NULL,\
    \diem REAL NOT NULL,\
    \usd REAL NOT NULL,\
    \effective REAL NOT NULL,\
    \consumption_rate REAL NOT NULL,\
    \time_to_depletion INTEGER\
    \)"
  
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_balance_history_timestamp ON balance_history(timestamp)"
  
  -- Proofs table
  execute_ conn "CREATE TABLE IF NOT EXISTS proofs (\
    \id TEXT PRIMARY KEY,\
    \theorem_name TEXT NOT NULL,\
    \file_path TEXT NOT NULL,\
    \line_start INTEGER NOT NULL,\
    \line_end INTEGER NOT NULL,\
    \statement TEXT NOT NULL,\
    \proof_text TEXT NOT NULL,\
    \status TEXT NOT NULL DEFAULT 'proven' CHECK (status IN ('proven', 'sorry', 'incomplete')),\
    \verified_at TEXT NOT NULL DEFAULT (datetime('now')),\
    \verified_by TEXT,\
    \dependencies TEXT,\
    \tags TEXT,\
    \description TEXT\
    \)"
  
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_proofs_theorem_name ON proofs(theorem_name)"
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_proofs_file_path ON proofs(file_path)"
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_proofs_status ON proofs(status)"
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_proofs_verified_at ON proofs(verified_at DESC)"
  
  -- Settings table
  execute_ conn "CREATE TABLE IF NOT EXISTS settings (\
    \key TEXT PRIMARY KEY,\
    \value TEXT NOT NULL,\
    \updated_at TEXT NOT NULL DEFAULT (datetime('now'))\
    \)"
  
  execute_ conn "CREATE INDEX IF NOT EXISTS idx_settings_updated_at ON settings(updated_at DESC)"
