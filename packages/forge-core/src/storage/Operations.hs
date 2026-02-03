-- | Database Operations
-- | SQLite operations for Bridge Server
{-# LANGUAGE OverloadedStrings #-}
module Bridge.Database.Operations where

import Database.SQLite.Simple
import Database.SQLite.Simple.FromRow
import Database.SQLite.Simple.ToRow
import Bridge.Database.Schema
import Data.Text (Text)
import Data.Time (UTCTime, getCurrentTime)
import Data.UUID (UUID)
import Data.UUID.V4 (nextRandom)
import qualified Data.Text as T
import qualified Data.UUID as UUID

-- | FromRow instance for ProofRecord
instance FromRow ProofRecord where
  fromRow = ProofRecord <$> field <*> field <*> field <*> field <*> field <*> field <*> field <*> field <*> field <*> field <*> field <*> field <*> field

-- | ToRow instance for ProofRecord
instance ToRow ProofRecord where
  toRow proof = toRow (proofId proof, proofTheoremName proof, proofFilePath proof, proofLineStart proof, proofLineEnd proof, proofStatement proof, proofText proof, proofStatus proof, proofVerifiedAt proof, proofVerifiedBy proof, proofDependencies proof, proofTags proof, proofDescription proof)

-- | Save snapshot
saveSnapshot :: Connection -> Snapshot -> IO Text
saveSnapshot conn snapshot = do
  execute conn
    "INSERT OR REPLACE INTO snapshots (id, timestamp, state_hash, data, trigger, description) VALUES (?, ?, ?, ?, ?, ?)"
    (snapshotId snapshot, snapshotTimestamp snapshot, snapshotStateHash snapshot, snapshotData snapshot, snapshotTrigger snapshot, snapshotDescription snapshot)
  return (snapshotId snapshot)

-- | Get snapshot by ID
getSnapshot :: Connection -> Text -> IO (Maybe Snapshot)
getSnapshot conn id = do
  results <- query conn
    "SELECT id, timestamp, state_hash, data, trigger, description FROM snapshots WHERE id = ?"
    (Only id)
  case results of
    [] -> return Nothing
    (r:_) -> return (Just r)

-- | List snapshots
listSnapshots :: Connection -> Maybe Int -> Maybe Int -> IO [Snapshot]
listSnapshots conn limit offset = do
  let limitVal = maybe 100 id limit
      offsetVal = maybe 0 id offset
  query conn
    "SELECT id, timestamp, state_hash, data, trigger, description FROM snapshots ORDER BY timestamp DESC LIMIT ? OFFSET ?"
    (limitVal, offsetVal)

-- | Delete snapshot
deleteSnapshot :: Connection -> Text -> IO Bool
deleteSnapshot conn id = do
  changes <- execute conn "DELETE FROM snapshots WHERE id = ?" (Only id)
  return (changes > 0)

-- | Save proof
saveProof :: Connection -> ProofRecord -> IO Text
saveProof conn proof = do
  execute conn
    "INSERT OR REPLACE INTO proofs (id, theorem_name, file_path, line_start, line_end, statement, proof_text, status, verified_at, verified_by, dependencies, tags, description) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)"
    (proofId proof, proofTheoremName proof, proofFilePath proof, proofLineStart proof, proofLineEnd proof, proofStatement proof, proofText proof, proofStatus proof, proofVerifiedAt proof, proofVerifiedBy proof, proofDependencies proof, proofTags proof, proofDescription proof)
  return (proofId proof)

-- | Get proof by ID
getProof :: Connection -> Text -> IO (Maybe ProofRecord)
getProof conn id = do
  results <- query conn
    "SELECT id, theorem_name, file_path, line_start, line_end, statement, proof_text, status, verified_at, verified_by, dependencies, tags, description FROM proofs WHERE id = ?"
    (Only id)
  case results of
    [] -> return Nothing
    (r:_) -> return (Just r)

-- | List proofs (with optional filters)
listProofs :: Connection -> Maybe Text -> Maybe Text -> Maybe Int -> Maybe Int -> IO [ProofRecord]
listProofs conn statusFilter fileFilter limit offset = do
  let limitVal = maybe 100 id limit
      offsetVal = maybe 0 id offset
      statusClause = maybe "" (\s -> " AND status = '" <> s <> "'") statusFilter
      fileClause = maybe "" (\f -> " AND file_path LIKE '%" <> f <> "%'") fileFilter
      whereClause = if statusClause == "" && fileClause == "" then "" else "WHERE 1=1" <> statusClause <> fileClause
  query conn
    ("SELECT id, theorem_name, file_path, line_start, line_end, statement, proof_text, status, verified_at, verified_by, dependencies, tags, description FROM proofs " <> whereClause <> " ORDER BY verified_at DESC LIMIT ? OFFSET ?")
    (limitVal, offsetVal)

-- | Get proofs by file path
getProofsByFile :: Connection -> Text -> IO [ProofRecord]
getProofsByFile conn filePath = do
  query conn
    "SELECT id, theorem_name, file_path, line_start, line_end, statement, proof_text, status, verified_at, verified_by, dependencies, tags, description FROM proofs WHERE file_path = ? ORDER BY line_start"
    (Only filePath)

-- | Delete proof
deleteProof :: Connection -> Text -> IO Bool
deleteProof conn id = do
  changes <- execute conn "DELETE FROM proofs WHERE id = ?" (Only id)
  return (changes > 0)

-- | Save session
saveSession :: Connection -> SessionRecord -> IO Text
saveSession conn session = do
  execute conn
    "INSERT OR REPLACE INTO sessions (id, session_id, prompt_tokens, completion_tokens, total_tokens, cost, model, provider, started_at, ended_at) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)"
    (sessionRecordId session, sessionRecordSessionId session, sessionRecordPromptTokens session, sessionRecordCompletionTokens session, sessionRecordTotalTokens session, sessionRecordCost session, sessionRecordModel session, sessionRecordProvider session, sessionRecordStartedAt session, sessionRecordEndedAt session)
  return (sessionRecordId session)

-- | Get sessions by session ID
getSessionsBySessionId :: Connection -> Text -> IO [SessionRecord]
getSessionsBySessionId conn sessionId = do
  query conn
    "SELECT id, session_id, prompt_tokens, completion_tokens, total_tokens, cost, model, provider, started_at, ended_at FROM sessions WHERE session_id = ? ORDER BY started_at DESC"
    (Only sessionId)

-- | Record balance history
recordBalanceHistory :: Connection -> Double -> Double -> Double -> Double -> Maybe Int -> IO Text
recordBalanceHistory conn diem usd effective consumptionRate timeToDepletion = do
  id <- UUID.toText <$> nextRandom
  timestamp <- getCurrentTime
  execute conn
    "INSERT INTO balance_history (id, timestamp, diem, usd, effective, consumption_rate, time_to_depletion) VALUES (?, ?, ?, ?, ?, ?, ?)"
    (id, timestamp, diem, usd, effective, consumptionRate, timeToDepletion)
  return id

-- | Get balance history
getBalanceHistory :: Connection -> Maybe Int -> Maybe Int -> IO [BalanceHistoryRecord]
getBalanceHistory conn limit offset = do
  let limitVal = maybe 100 id limit
      offsetVal = maybe 0 id offset
  query conn
    "SELECT id, timestamp, diem, usd, effective, consumption_rate, time_to_depletion FROM balance_history ORDER BY timestamp DESC LIMIT ? OFFSET ?"
    (limitVal, offsetVal)

-- | Instance definitions for FromRow
instance FromRow Snapshot where
  fromRow = Snapshot <$> field <*> field <*> field <*> field <*> field <*> field

instance FromRow SessionRecord where
  fromRow = SessionRecord <$> field <*> field <*> field <*> field <*> field <*> field <*> field <*> field <*> field <*> field

instance FromRow BalanceHistoryRecord where
  fromRow = BalanceHistoryRecord <$> field <*> field <*> field <*> field <*> field <*> field <*> field

-- | Instance definitions for ToRow
instance ToRow Snapshot where
  toRow s = toRow (snapshotId s, snapshotTimestamp s, snapshotStateHash s, snapshotData s, snapshotTrigger s, snapshotDescription s)

instance ToRow SessionRecord where
  toRow s = toRow (sessionRecordId s, sessionRecordSessionId s, sessionRecordPromptTokens s, sessionRecordCompletionTokens s, sessionRecordTotalTokens s, sessionRecordCost s, sessionRecordModel s, sessionRecordProvider s, sessionRecordStartedAt s, sessionRecordEndedAt s)

instance ToRow BalanceHistoryRecord where
  toRow b = toRow (balanceHistoryId b, balanceHistoryTimestamp b, balanceHistoryDiem b, balanceHistoryUsd b, balanceHistoryEffective b, balanceHistoryConsumptionRate b, balanceHistoryTimeToDepletion b)

-- | Save settings
saveSettings :: Connection -> Text -> Text -> IO ()
saveSettings conn key value = do
  timestamp <- getCurrentTime
  execute conn
    "INSERT OR REPLACE INTO settings (key, value, updated_at) VALUES (?, ?, ?)"
    (key, value, timestamp)

-- | Get settings
getSettings :: Connection -> Text -> IO (Maybe Text)
getSettings conn key = do
  results <- query conn
    "SELECT value FROM settings WHERE key = ?"
    (Only key)
  case results of
    [] -> return Nothing
    (Only val:_) -> return (Just val)
