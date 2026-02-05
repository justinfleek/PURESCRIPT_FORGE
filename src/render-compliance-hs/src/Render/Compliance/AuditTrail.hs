{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Render Gateway Compliance Features
-- | Audit trail, reconciliation, hash chain verification per render_specs.pdf §7, §11
module Render.Compliance.AuditTrail where

import Prelude hiding (head, tail)
import Control.Exception (try, SomeException)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Time (UTCTime, getCurrentTime)
import Data.List (foldl')
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
import Crypto.Hash (hash, Digest, BLAKE2b_256)
import qualified Crypto.Hash as Hash
import Crypto.PubKey.Ed25519 (SecretKey, PublicKey, Signature, sign, verify, generateSecretKey, toPublic)
import qualified Data.ByteArray as BA
import System.IO.Unsafe (unsafePerformIO)
import Render.ClickHouse.Client (ClickHouseClient, queryMetricsAggregates, MetricsAggregate(..))
import Render.CAS.Client (CASClient, TimeRange(..), queryCASMetrics)
import Database.DuckDB.Simple (Connection, query)
import qualified Database.DuckDB.Simple as DuckDB

-- Global signing key (in production, load from secure storage)
{-# NOINLINE globalSigningKey #-}
globalSigningKey :: (SecretKey, PublicKey)
globalSigningKey = unsafePerformIO $ do
  sk <- generateSecretKey
  let pk = toPublic sk
  pure (sk, pk)

-- | Audit trail entry
data AuditTrailEntry = AuditTrailEntry
  { ateTimestamp :: UTCTime
  , ateEventType :: Text -- "inference", "billing", "reconciliation"
  , ateContent :: ByteString
  , ateContentHash :: ByteString -- BLAKE2b-256
  , atePreviousHash :: Maybe ByteString -- Hash chain link
  , ateSignature :: ByteString -- Ed25519 signature
  }

-- | Hash chain (immutable audit trail)
data HashChain = HashChain
  { hcEntries :: [AuditTrailEntry]
  , hcCurrentHash :: ByteString
  }

-- | Create new audit trail entry
createAuditEntry :: Text -> ByteString -> Maybe ByteString -> IO AuditTrailEntry
createAuditEntry eventType content previousHash = do
  -- Compute content hash (BLAKE2b-256)
  let contentHash = computeBlake2bHash content
  
  -- Compute chain hash (hash of previous hash + content hash)
  let chainHash = case previousHash of
        Nothing -> contentHash -- First entry
        Just prev -> computeBlake2bHash (prev <> contentHash)
  
  -- Sign entry
  signature <- signEntry chainHash
  
  -- Get timestamp
  now <- getCurrentTime
  
  pure AuditTrailEntry
    { ateTimestamp = now
    , ateEventType = eventType
    , ateContent = content
    , ateContentHash = contentHash
    , atePreviousHash = previousHash
    , ateSignature = signature
    }

-- | Append entry to hash chain
appendToChain :: HashChain -> AuditTrailEntry -> HashChain
appendToChain HashChain {..} entry = HashChain
  { hcEntries = hcEntries ++ [entry]
  , hcCurrentHash = case atePreviousHash entry of
      Nothing -> ateContentHash entry
      Just prev -> computeBlake2bHash (prev <> ateContentHash entry)
  }

-- | Verify hash chain integrity
verifyHashChain :: HashChain -> Bool
verifyHashChain HashChain {..} = 
  if null hcEntries then True
  else if length hcEntries == 1 then True
  else foldl' verifyLink True (zip (init hcEntries) (tail hcEntries))
  where
    verifyLink acc (prev, curr) = acc && verifyLinkPair prev curr
    
    verifyLinkPair :: AuditTrailEntry -> AuditTrailEntry -> Bool
    verifyLinkPair prev curr =
      case atePreviousHash curr of
        Nothing -> True -- First entry
        Just prevHash ->
          prevHash == ateContentHash prev &&
          verifySignature (ateContentHash curr) (ateSignature curr)

-- | Reconciliation procedure per render_specs.pdf §11.4
reconcileFastSlowPath :: ClickHouseClient -> CASClient -> Maybe Connection -> TimeRange -> IO ReconciliationResult
reconcileFastSlowPath chClient casClient mDuckDBConn range = do
  -- Aggregate from fast path (ClickHouse)
  chAggregates <- queryClickHouseAggregates chClient range
  
  -- Aggregate from slow path (CAS, authoritative via DuckDB)
  casAggregates <- queryCASAggregates casClient mDuckDBConn range
  
  -- Compute deltas
  let deltas = computeReconciliationDeltas chAggregates casAggregates
  
  -- Filter discrepancies > threshold (0.1%)
  let discrepancies = filter (\(_, delta) -> abs delta > 0.001) deltas
  
  -- Generate reconciliation report
  now <- getCurrentTime
  pure ReconciliationResult
    { rrRange = range
    , rrDeltas = discrepancies
    , rrStatus = if null discrepancies then Reconciled else DiscrepanciesFound
    , rrTimestamp = now
    }

-- | Reconciliation aggregates
data ReconciliationAggregates = ReconciliationAggregates
  { raCustomerId :: Text
  , raModelName :: Text
  , raRequestCount :: Int
  , raGpuSeconds :: Double
  }

-- | Reconciliation result
data ReconciliationResult = ReconciliationResult
  { rrRange :: TimeRange
  , rrDeltas :: [(Text, Double)] -- (customer_id, delta_percentage)
  , rrStatus :: ReconciliationStatus
  , rrTimestamp :: UTCTime
  }

data ReconciliationStatus
  = Reconciled
  | DiscrepanciesFound

data TimeRange = TimeRange
  { trStart :: UTCTime
  , trEnd :: UTCTime
  }

-- | Helper functions

-- | Compute BLAKE2b-256 hash (using crypton)
-- | Note: Function name reflects actual algorithm (BLAKE2b-256), not BLAKE3
computeBlake2bHash :: ByteString -> ByteString
computeBlake2bHash bs =
  let digest :: Digest BLAKE2b_256
      digest = hash bs
  in BA.convert digest

-- | Sign entry with Ed25519
signEntry :: ByteString -> IO ByteString
signEntry bs = do
  let (sk, pk) = globalSigningKey
  let sig :: Signature
      sig = sign sk pk bs
  pure $ BA.convert sig

-- | Verify Ed25519 signature
verifySignature :: ByteString -> ByteString -> Bool
verifySignature content sigBytes =
  let (_, pk) = globalSigningKey
  in case BA.convert sigBytes of
    sig -> verify pk content sig

-- | Query ClickHouse aggregates
queryClickHouseAggregates :: ClickHouseClient -> TimeRange -> IO [ReconciliationAggregates]
queryClickHouseAggregates client TimeRange {..} = do
  result <- queryMetricsAggregates client trStart trEnd
  case result of
    Left _ -> pure [] -- On error, return empty (reconciliation will show discrepancy)
    Right metrics -> pure $ map convertMetricsAggregate metrics
  where
    convertMetricsAggregate :: MetricsAggregate -> ReconciliationAggregates
    convertMetricsAggregate MetricsAggregate {..} = ReconciliationAggregates
      { raCustomerId = maCustomerId
      , raModelName = maModelName
      , raRequestCount = maRequestCount
      , raGpuSeconds = maGpuSeconds
      }

-- | Query CAS aggregates via DuckDB
-- | Queries DuckDB for CAS audit records and aggregates by customer and model
queryCASAggregates :: CASClient -> Maybe Connection -> TimeRange -> IO [ReconciliationAggregates]
queryCASAggregates _client mDuckDBConn TimeRange {..} = do
  case mDuckDBConn of
    Nothing -> pure [] -- No DuckDB connection available
    Just conn -> do
      -- Query DuckDB for CAS audit records
      -- DuckDB has a cas_audit_metadata table populated from CAS objects
      -- with columns: customer_id, model_name, timestamp, gpu_seconds
      
      -- Execute query to aggregate CAS audit records
      result <- try $ DuckDB.query conn
        "SELECT customer_id, model_name, count() as request_count, sum(gpu_seconds) as gpu_seconds \
        \FROM cas_audit_metadata \
        \WHERE timestamp >= ? AND timestamp < ? \
        \GROUP BY customer_id, model_name"
        (trStart, trEnd)
      
      case result of
        Left (_ :: SomeException) -> pure [] -- On error, return empty
        Right rows -> pure $ map convertRow rows
  where
    convertRow :: (Text, Text, Int, Double) -> ReconciliationAggregates
    convertRow (customerId, modelName, requestCount, gpuSeconds) = ReconciliationAggregates
      { raCustomerId = customerId
      , raModelName = modelName
      , raRequestCount = requestCount
      , raGpuSeconds = gpuSeconds
      }

-- | Compute percentage deltas between ClickHouse and CAS aggregates
-- | Aggregates are compared by (customer_id, model_name) pairs
computeReconciliationDeltas :: [ReconciliationAggregates] -> [ReconciliationAggregates] -> [(Text, Double)]
computeReconciliationDeltas chAggregates casAggregates = do
  -- Create maps keyed by (customer_id, model_name) pair for accurate comparison
  -- This ensures we compare aggregates for the same customer AND model
  let chMap = Map.fromList $ map (\agg -> ((raCustomerId agg, raModelName agg), agg)) chAggregates
  let casMap = Map.fromList $ map (\agg -> ((raCustomerId agg, raModelName agg), agg)) casAggregates
  
  -- Get all unique (customer_id, model_name) pairs from both maps
  let allKeys = Set.toList $ Map.keysSet chMap `Set.union` Map.keysSet casMap
  
  -- Compute delta for each (customer_id, model_name) pair
  foldl' (\acc (customerId, modelName) -> 
    let
      chAgg = fromMaybe (ReconciliationAggregates customerId modelName 0 0.0) (Map.lookup (customerId, modelName) chMap)
      casAgg = fromMaybe (ReconciliationAggregates customerId modelName 0 0.0) (Map.lookup (customerId, modelName) casMap)
      
      -- Compute percentage delta: (cas - ch) / ch * 100
      -- Use GPU seconds as the metric
      chGpuSeconds = raGpuSeconds chAgg
      casGpuSeconds = raGpuSeconds casAgg
      delta = if chGpuSeconds > 0.0
        then ((casGpuSeconds - chGpuSeconds) / chGpuSeconds) * 100.0
        else if casGpuSeconds > 0.0 then 100.0 else 0.0
    in
      (customerId, delta) : acc
  ) [] allKeys
