{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Render Gateway Compliance Features
-- | Audit trail, reconciliation, hash chain verification per render_specs.pdf §7, §11
module Render.Compliance.AuditTrail where

import Prelude hiding (head, tail)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Time (UTCTime, getCurrentTime)
import Data.List (foldl')
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe)

-- | Audit trail entry
data AuditTrailEntry = AuditTrailEntry
  { ateTimestamp :: UTCTime
  , ateEventType :: Text -- "inference", "billing", "reconciliation"
  , ateContent :: ByteString
  , ateContentHash :: ByteString -- BLAKE3
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
  -- Compute content hash (BLAKE3)
  let contentHash = computeBlake3Hash content
  
  -- Compute chain hash (hash of previous hash + content hash)
  let chainHash = case previousHash of
        Nothing -> contentHash -- First entry
        Just prev -> computeBlake3Hash (prev <> contentHash)
  
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
      Just prev -> computeBlake3Hash (prev <> ateContentHash entry)
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
reconcileFastSlowPath :: TimeRange -> IO ReconciliationResult
reconcileFastSlowPath range = do
  -- Aggregate from fast path (ClickHouse)
  chAggregates <- queryClickHouseAggregates range
  
  -- Aggregate from slow path (CAS, authoritative)
  casAggregates <- queryCASAggregates range
  
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

-- | Compute BLAKE3 hash (placeholder implementation)
computeBlake3Hash :: ByteString -> ByteString
computeBlake3Hash bs = 
  -- TODO: Use blake3 library when available
  -- import qualified Crypto.Hash.Blake3 as B3
  -- B3.hash bs
  BS.pack [0] -- Placeholder: returns single zero byte

-- | Sign entry with Ed25519 (placeholder implementation)
signEntry :: ByteString -> IO ByteString
signEntry bs = do
  -- TODO: Use ed25519 library when available
  -- import qualified Crypto.Sign.Ed25519 as Ed25519
  -- key <- Ed25519.generateSecretKey
  -- pure $ Ed25519.sign key bs
  pure $ BS.pack [0] -- Placeholder: returns single zero byte

-- | Verify Ed25519 signature (placeholder implementation)
verifySignature :: ByteString -> ByteString -> Bool
verifySignature _content _signature = 
  -- TODO: Use ed25519 library when available
  -- import qualified Crypto.Sign.Ed25519 as Ed25519
  -- Ed25519.verify publicKey content signature
  False -- Placeholder: always returns False

-- | Query ClickHouse aggregates (placeholder implementation)
queryClickHouseAggregates :: TimeRange -> IO [ReconciliationAggregates]
queryClickHouseAggregates _range = do
  -- TODO: Implement actual ClickHouse query
  -- For now, return empty list
  pure []

-- | Query CAS aggregates via DuckDB (placeholder implementation)
queryCASAggregates :: TimeRange -> IO [ReconciliationAggregates]
queryCASAggregates _range = do
  -- TODO: Implement actual CAS/DuckDB query
  -- For now, return empty list
  pure []

-- | Compute percentage deltas between ClickHouse and CAS aggregates
computeReconciliationDeltas :: [ReconciliationAggregates] -> [ReconciliationAggregates] -> [(Text, Double)]
computeReconciliationDeltas chAggregates casAggregates = do
  -- Create maps keyed by customer ID for efficient lookup
  let chMap = Map.fromList $ map (\agg -> (raCustomerId agg, agg)) chAggregates
  let casMap = Map.fromList $ map (\agg -> (raCustomerId agg, agg)) casAggregates
  
  -- Get all unique customer IDs from both maps
  let allCustomerIds = Map.keysSet chMap `Map.union` Map.keysSet casMap
  
  -- Compute delta for each customer
  Map.foldlWithKey (\acc customerId _ -> 
    let
      chAgg = fromMaybe (ReconciliationAggregates customerId "" 0 0.0) (Map.lookup customerId chMap)
      casAgg = fromMaybe (ReconciliationAggregates customerId "" 0 0.0) (Map.lookup customerId casMap)
      
      -- Compute percentage delta: (cas - ch) / ch * 100
      -- Use GPU seconds as the metric
      chGpuSeconds = raGpuSeconds chAgg
      casGpuSeconds = raGpuSeconds casAgg
      delta = if chGpuSeconds > 0.0
        then ((casGpuSeconds - chGpuSeconds) / chGpuSeconds) * 100.0
        else if casGpuSeconds > 0.0 then 100.0 else 0.0
    in
      (customerId, delta) : acc
  ) [] allCustomerIds
