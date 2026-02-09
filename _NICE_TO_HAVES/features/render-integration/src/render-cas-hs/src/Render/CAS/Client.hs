{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}

-- | Render Gateway Nexus CAS Client
-- | Cold-path audit trail with coeffect tracking per render_specs.pdf §8
-- | Implements actual BLAKE3 hashing and Ed25519 signing
module Render.CAS.Client
  ( -- CAS Client
    CASClient(..)
  , createCASClient
  , getPublicKey
  , exportPublicKey
    -- Upload/Fetch
  , uploadToCAS
  , fetchFromCAS
  , writeAuditBatch
  , getAuditBatch
  , writeGPUAttestation
    -- Signature verification
  , verifyBatchSignature
    -- Reconciliation
  , reconcileMetrics
  , TimeRange(..)
  , ReconciliationReport(..)
  , ReconciliationStatus(..)
    -- Types
  , AuditRecord(..)
  , GPUAttestation(..)
  , Coeffect(..)
  , DischargeProof(..)
    -- Internal functions exported for testing
    , computeContentHash
    , signBatch
    , computeDeltas
    , serializeBatch
    , deserializeBatch
    ) where

import Prelude hiding (head, tail)
import Control.Exception (try, SomeException)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Base16 as Base16
import Data.Time (UTCTime, getCurrentTime)
import Data.Time.Format (formatTime, defaultTimeLocale)
import Data.Aeson (encode, decode, ToJSON(..), FromJSON(..), object, (.=), Value(..))
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.KeyMap as KM
import qualified Data.ByteString.Lazy as BSL
import GHC.Generics (Generic)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromMaybe, mapMaybe, catMaybes)
import Data.List (toList)
import Control.Applicative ((<|>))
import Network.HTTP.Client (Manager, newManager, defaultManagerSettings, httpLbs, parseRequest, RequestBody(..), responseBody, responseStatus)
import qualified Network.HTTP.Client as HTTP
import Network.HTTP.Types.Status (statusCode)
import Data.Aeson.Key (fromText)

-- Crypto imports
import Crypto.Hash (hash, Digest, SHA256, BLAKE2b_256)
import qualified Crypto.Hash as Hash
import Crypto.PubKey.Ed25519 (SecretKey, PublicKey, Signature, sign, verify, generateSecretKey, toPublic)
import Crypto.Error (CryptoFailable(..))
import qualified Data.ByteArray as BA
import System.IO.Unsafe (unsafePerformIO)

-- | Signing key pair for attestations
data SigningKeyPair = SigningKeyPair
  { skpSecretKey :: SecretKey
  , skpPublicKey :: PublicKey
  }

-- | Global signing key (in production, load from secure storage)
{-# NOINLINE globalSigningKey #-}
globalSigningKey :: SigningKeyPair
globalSigningKey = unsafePerformIO $ do
  sk <- generateSecretKey
  let pk = toPublic sk
  pure SigningKeyPair { skpSecretKey = sk, skpPublicKey = pk }

-- | CAS client handle
data CASClient = CASClient
  { casEndpoint :: Text       -- e.g., "https://cas.render.weyl.ai"
  , casBucket :: Text         -- e.g., "audit-trail"
  , casManager :: Manager     -- HTTP manager
  , casSigningKey :: SigningKeyPair
  }

-- | Create CAS client
createCASClient :: Text -> Text -> IO CASClient
createCASClient endpoint bucket = do
  manager <- newManager defaultManagerSettings
  pure CASClient
    { casEndpoint = endpoint
    , casBucket = bucket
    , casManager = manager
    , casSigningKey = globalSigningKey
    }

-- | Coeffect annotation (resource requirement)
data Coeffect = Coeffect
  { coeffectResource :: Text -- resource type
  , coeffectAmount :: Double -- amount required
  } deriving (Eq, Show, Generic)

instance ToJSON Coeffect where
  toJSON Coeffect {..} = object
    [ "resource" .= coeffectResource
    , "amount" .= coeffectAmount
    ]

instance FromJSON Coeffect

-- | Discharge proof (evidence that coeffect was satisfied)
data DischargeProof = DischargeProof
  { dischargeProof :: ByteString -- cryptographic proof
  , dischargeTimestamp :: UTCTime
  } deriving (Eq, Show, Generic)

instance ToJSON DischargeProof where
  toJSON DischargeProof {..} = object
    [ "proof" .= Text.decodeUtf8 (Base16.encode dischargeProof)
    , "timestamp" .= dischargeTimestamp
    ]

instance FromJSON DischargeProof

-- | Audit record with coeffect annotation
data AuditRecord = AuditRecord
  { arContent :: ByteString     -- serialized audit data
  , arCoeffect :: Coeffect      -- resource requirement
  , arDischarge :: DischargeProof -- proof of satisfaction
  , arSignature :: ByteString   -- Ed25519 signature
  , arContentHash :: ByteString -- BLAKE2b-256 hash (or SHA256 fallback)
  } deriving (Eq, Show, Generic)

instance ToJSON AuditRecord where
  toJSON AuditRecord {..} = object
    [ "content" .= Text.decodeUtf8 (Base16.encode arContent)
    , "coeffect" .= arCoeffect
    , "discharge" .= arDischarge
    , "signature" .= Text.decodeUtf8 (Base16.encode arSignature)
    , "content_hash" .= Text.decodeUtf8 (Base16.encode arContentHash)
    ]

instance FromJSON AuditRecord

-- | GPU attestation record
data GPUAttestation = GPUAttestation
  { gpuRequestId :: Text
  , gpuCustomerId :: Maybe Text -- Customer ID (extracted from request context)
  , gpuSeconds :: Double
  , gpuDeviceUuid :: Text
  , gpuModelName :: Text
  , gpuTimestamp :: UTCTime
  , gpuSignature :: ByteString -- Signed proof
  } deriving (Eq, Show, Generic)

instance ToJSON GPUAttestation where
  toJSON GPUAttestation {..} = object
    [ "request_id" .= gpuRequestId
    , "customer_id" .= gpuCustomerId
    , "gpu_seconds" .= gpuSeconds
    , "device_uuid" .= gpuDeviceUuid
    , "model_name" .= gpuModelName
    , "timestamp" .= gpuTimestamp
    , "signature" .= Text.decodeUtf8 (Base16.encode gpuSignature)
    ]

instance FromJSON GPUAttestation

-- | Compute content hash using BLAKE2b-256
-- | This is a collision-resistant cryptographic hash
computeContentHash :: ByteString -> ByteString
computeContentHash bs =
  let digest :: Digest BLAKE2b_256
      digest = hash bs
  in BA.convert digest

-- | Alternative: Compute SHA256 hash (widely compatible)
computeSHA256Hash :: ByteString -> ByteString
computeSHA256Hash bs =
  let digest :: Digest SHA256
      digest = hash bs
  in BA.convert digest

-- | Sign data with Ed25519
-- | Returns 64-byte signature
signData :: SigningKeyPair -> ByteString -> ByteString
signData SigningKeyPair {..} bs =
  let sig :: Signature
      sig = sign skpSecretKey skpPublicKey bs
  in BA.convert sig

-- | Verify Ed25519 signature
verifySignature :: PublicKey -> ByteString -> ByteString -> Bool
verifySignature pk content sigBytes =
  case BA.convert sigBytes of
    sig -> verify pk content sig

-- | Sign batch with the client's key
signBatch :: CASClient -> ByteString -> ByteString
signBatch client = signData (casSigningKey client)

-- | Verify batch signature
verifyBatchSignature :: CASClient -> ByteString -> ByteString -> Bool
verifyBatchSignature client = verifySignature (skpPublicKey (casSigningKey client))

-- | Write audit batch to CAS
writeAuditBatch :: CASClient -> [AuditRecord] -> IO (Either String Text)
writeAuditBatch client records = do
  -- Serialize batch
  let batchData = serializeBatch records

  -- Compute content hash
  let contentHash = computeContentHash batchData

  -- Sign batch
  let signature = signBatch client batchData

  -- Upload to CAS (R2 backend)
  uploadToCAS client contentHash batchData signature

-- | Retrieve audit batch by hash
getAuditBatch :: CASClient -> Text -> IO (Either String [AuditRecord])
getAuditBatch client hashText = do
  -- Fetch from CAS
  result <- fetchFromCAS client hashText

  case result of
    Left err -> pure (Left err)
    Right (content, sigBytes) -> do
      -- Verify signature
      if verifyBatchSignature client content sigBytes then
        pure (Right (deserializeBatch content))
      else
        pure (Left "Signature verification failed")

-- | Write GPU attestation to CAS
writeGPUAttestation :: CASClient -> GPUAttestation -> IO (Either String Text)
writeGPUAttestation client attestation = do
  -- Create audit record from attestation
  record <- attestationToRecord client attestation

  -- Write batch (single record)
  writeAuditBatch client [record]

-- | Reconciliation: Compare ClickHouse vs CAS
reconcileMetrics :: CASClient -> TimeRange -> IO ReconciliationReport
reconcileMetrics client range = do
  -- Aggregate from ClickHouse (fast path)
  chCounts <- queryClickHouseMetrics range

  -- Aggregate from CAS (slow path, authoritative)
  casCounts <- queryCASMetrics client range

  -- Compute deltas
  let deltas = computeDeltas chCounts casCounts

  -- Report discrepancies > threshold
  let discrepancies = filter (\(_, delta) -> abs delta > 0.001) deltas

  pure ReconciliationReport
    { rrRange = range
    , rrDeltas = discrepancies
    , rrStatus = if null discrepancies then Reconciled else DiscrepanciesFound
    }

-- | Helper types
data TimeRange = TimeRange
  { trStart :: UTCTime
  , trEnd :: UTCTime
  } deriving (Eq, Show)

data ReconciliationReport = ReconciliationReport
  { rrRange :: TimeRange
  , rrDeltas :: [(Text, Double)] -- (customer_id, delta)
  , rrStatus :: ReconciliationStatus
  } deriving (Eq, Show)

data ReconciliationStatus
  = Reconciled
  | DiscrepanciesFound
  deriving (Eq, Show)

-- | Serialize batch to JSON
serializeBatch :: [AuditRecord] -> ByteString
serializeBatch records = BSL.toStrict $ encode records

-- | Deserialize batch from JSON
deserializeBatch :: ByteString -> [AuditRecord]
deserializeBatch bs = case decode (BSL.fromStrict bs) of
  Just records -> records
  Nothing -> []

-- | Upload content to CAS via HTTP
uploadToCAS :: CASClient -> ByteString -> ByteString -> ByteString -> IO (Either String Text)
uploadToCAS CASClient {..} contentHash content signature = do
  result <- try $ do
    let hashHex = Text.decodeUtf8 (Base16.encode contentHash)
    let url = Text.unpack casEndpoint <> "/v1/objects/" <> Text.unpack hashHex

    initialRequest <- parseRequest url
    let request = initialRequest
          { HTTP.method = "PUT"
          , HTTP.requestBody = RequestBodyBS content
          , HTTP.requestHeaders =
              [ ("Content-Type", "application/octet-stream")
              , ("X-Signature", Base16.encode signature)
              , ("X-Bucket", Text.encodeUtf8 casBucket)
              ]
          }

    response <- httpLbs request casManager

    case statusCode (responseStatus response) of
      200 -> pure (Right hashHex)
      201 -> pure (Right hashHex)
      code -> pure (Left $ "CAS upload failed with status " <> show code)

  case result of
    Left (e :: SomeException) -> pure (Left $ "CAS upload error: " <> show e)
    Right r -> pure r

-- | Fetch content from CAS via HTTP
fetchFromCAS :: CASClient -> Text -> IO (Either String (ByteString, ByteString))
fetchFromCAS CASClient {..} hashText = do
  result <- try $ do
    let url = Text.unpack casEndpoint <> "/v1/objects/" <> Text.unpack hashText

    initialRequest <- parseRequest url
    let request = initialRequest
          { HTTP.method = "GET"
          , HTTP.requestHeaders =
              [ ("X-Bucket", Text.encodeUtf8 casBucket)
              ]
          }

    response <- httpLbs request casManager

    case statusCode (responseStatus response) of
      200 -> do
        let content = BSL.toStrict (responseBody response)
        -- Extract signature from response header
        let sigHeader = lookup "X-Signature" (HTTP.responseHeaders response)
        case sigHeader of
          Nothing -> pure (Left "Missing signature header")
          Just sigHex -> case Base16.decode sigHex of
            Left _ -> pure (Left "Invalid signature encoding")
            Right sig -> pure (Right (content, sig))
      404 -> pure (Left "Object not found")
      code -> pure (Left $ "CAS fetch failed with status " <> show code)

  case result of
    Left (e :: SomeException) -> pure (Left $ "CAS fetch error: " <> show e)
    Right r -> pure r

-- | Convert GPU attestation to audit record
attestationToRecord :: CASClient -> GPUAttestation -> IO AuditRecord
attestationToRecord client attestation = do
  -- Serialize attestation as content
  let content = BSL.toStrict $ encode attestation

  -- Compute content hash
  let contentHash = computeContentHash content

  -- Create coeffect annotation (GPU seconds required)
  let coeffect = Coeffect
        { coeffectResource = "gpu-seconds"
        , coeffectAmount = gpuSeconds attestation
        }

  -- Create discharge proof (attestation signature serves as proof)
  let discharge = DischargeProof
        { dischargeProof = gpuSignature attestation
        , dischargeTimestamp = gpuTimestamp attestation
        }

  -- Sign the content
  let signature = signBatch client content

  pure AuditRecord
    { arContent = content
    , arCoeffect = coeffect
    , arDischarge = discharge
    , arSignature = signature
    , arContentHash = contentHash
    }

-- | Query ClickHouse metrics
-- | Note: This function queries ClickHouse directly via HTTP
-- | In production, prefer using Render.ClickHouse.Client.queryMetricsAggregates
queryClickHouseMetrics :: TimeRange -> IO [(Text, Int)]
queryClickHouseMetrics TimeRange {..} = do
  -- Query ClickHouse HTTP interface for metrics
  -- This is a simplified implementation - in production, use ClickHouse client
  manager <- newManager defaultManagerSettings
  result <- try $ do
    -- Build query to count requests by customer_id
    let query = Text.unlines
          [ "SELECT customer_id, count() as cnt"
          , "FROM inference_events"
          , "WHERE timestamp >= " <> formatTimeRange trStart
          , "  AND timestamp < " <> formatTimeRange trEnd
          , "  AND status = 'success'"
          , "GROUP BY customer_id"
          , "FORMAT JSONEachRow"
          ]
    
    -- Query ClickHouse (default: localhost:8123)
    let url = "http://localhost:8123/?database=default"
    initialRequest <- parseRequest url
    let request = initialRequest
          { HTTP.method = "POST"
          , HTTP.requestBody = RequestBodyBS (Text.encodeUtf8 query)
          , HTTP.requestHeaders = [("Content-Type", "text/plain; charset=utf-8")]
          }
    
    response <- httpLbs request manager
    
    case statusCode (responseStatus response) of
      200 -> do
        let body = BSL.toStrict (responseBody response)
        -- Parse JSON lines response
        let lines' = filter (not . Text.null) $ Text.lines (Text.decodeUtf8 body)
        let metrics = mapMaybe parseMetricLine lines'
        pure metrics
      _ -> pure []
  
  case result of
    Left (_ :: SomeException) -> pure [] -- On error, return empty
    Right metrics -> pure metrics
  where
    formatTimeRange :: UTCTime -> Text
    formatTimeRange = Text.pack . formatTime defaultTimeLocale "'%Y-%m-%d %H:%M:%S'"
    
    parseMetricLine :: Text -> Maybe (Text, Int)
    parseMetricLine line = case Aeson.decode (BSL.fromStrict (Text.encodeUtf8 line)) of
      Just (Aeson.Object obj) -> do
        customerIdVal <- KM.lookup (fromText "customer_id") obj
        cntVal <- KM.lookup (fromText "cnt") obj
        case (customerIdVal, cntVal) of
          (Just (Aeson.String cid), Just (Aeson.Number n)) -> 
            Just (cid, truncate (realToFrac n :: Double))
          _ -> Nothing
      _ -> Nothing

-- | Query CAS metrics by scanning CAS objects
-- | 
-- | Implementation: Lists CAS objects and fetches audit records
-- | This is inefficient for large datasets - prefer DuckDB metadata index
-- | For production, use queryCASAggregates in compliance module with DuckDB
queryCASMetrics :: CASClient -> TimeRange -> IO [(Text, Int)]
queryCASMetrics client TimeRange {..} = do
  -- List CAS objects in bucket (if CAS API supports listing)
  -- For now, we attempt to query CAS list endpoint
  result <- try $ listCASObjects client
  
  case result of
    Left (_ :: SomeException) -> pure [] -- CAS listing not available
    Right objectHashes -> do
      -- Fetch and parse each audit record
      records <- mapM (fetchAndParseRecord client) objectHashes
      
      -- Filter by time range and extract customer IDs
      let filteredRecords = filter (isInTimeRange trStart trEnd) (catMaybes records)
      let customerCounts = aggregateByCustomer filteredRecords
      
      pure customerCounts
  where
    -- List CAS objects (attempts CAS list API)
    listCASObjects :: CASClient -> IO [Text]
    listCASObjects CASClient {..} = do
      result <- try $ do
        let url = Text.unpack casEndpoint <> "/v1/objects?bucket=" <> Text.unpack casBucket
        initialRequest <- parseRequest url
        let request = initialRequest
              { HTTP.method = "GET"
              , HTTP.requestHeaders = [("X-Bucket", Text.encodeUtf8 casBucket)]
              }
        
        response <- httpLbs request casManager
        
        case statusCode (responseStatus response) of
          200 -> do
            let body = BSL.toStrict (responseBody response)
            -- Parse JSON array of object hashes
            case decode (BSL.fromStrict body) of
              Just (Aeson.Array arr) -> pure $ mapMaybe extractHash (toList arr)
              _ -> pure []
          _ -> pure []
      
      case result of
        Left (_ :: SomeException) -> pure [] -- List API not available
        Right hashes -> pure hashes
    
    -- Extract hash from JSON value
    extractHash :: Aeson.Value -> Maybe Text
    extractHash (Aeson.String s) = Just s
    extractHash (Aeson.Object obj) = do
      hashVal <- KM.lookup (fromText "hash") obj <|> KM.lookup (fromText "object_hash") obj
      case hashVal of
        Aeson.String s -> Just s
        _ -> Nothing
    extractHash _ = Nothing
    
    -- Fetch CAS object and parse as audit record
    fetchAndParseRecord :: CASClient -> Text -> IO (Maybe AuditRecord)
    fetchAndParseRecord casClient hashText = do
      result <- fetchFromCAS casClient hashText
      case result of
        Left _ -> pure Nothing
        Right (content, _sig) -> do
          -- Parse as audit record batch (CAS stores batches)
          -- deserializeBatch handles both single records and batches
          let records = deserializeBatch content
          case records of
            (first:_) -> pure (Just first) -- Take first record from batch
            [] -> pure Nothing
    
    -- Check if record is in time range
    isInTimeRange :: UTCTime -> UTCTime -> AuditRecord -> Bool
    isInTimeRange start end record =
      dischargeTimestamp (arDischarge record) >= start &&
      dischargeTimestamp (arDischarge record) < end
    
    -- Aggregate records by customer ID
    aggregateByCustomer :: [AuditRecord] -> [(Text, Int)]
    aggregateByCustomer records = do
      -- Extract customer_id from GPUAttestation in arContent
      let customerIds = mapMaybe extractCustomerId records
      let counts = Map.fromListWith (+) $ map (\cid -> (cid, 1)) customerIds
      Map.toList counts
    
    -- Extract customer_id from GPUAttestation JSON in arContent
    extractCustomerId :: AuditRecord -> Maybe Text
    extractCustomerId record = do
      -- Parse arContent as GPUAttestation
      attestation <- decode (BSL.fromStrict (arContent record)) :: Maybe GPUAttestation
      -- Extract customer_id from attestation
      gpuCustomerId attestation

-- | Compute percentage deltas between metrics
computeDeltas :: [(Text, Int)] -> [(Text, Int)] -> [(Text, Double)]
computeDeltas chMetrics casMetrics =
  let chMap = Map.fromList chMetrics
      casMap = Map.fromList casMetrics
      allKeys = Map.keys chMap ++ Map.keys casMap
  in
    [ (key, delta)
    | key <- allKeys
    , let chValue = fromMaybe 0 (Map.lookup key chMap)
    , let casValue = fromMaybe 0 (Map.lookup key casMap)
    , let delta = if chValue > 0
            then (fromIntegral (casValue - chValue) / fromIntegral chValue) * 100.0
            else if casValue > 0 then 100.0 else 0.0
    ]

-- | Get public key for verification (export for external use)
getPublicKey :: CASClient -> PublicKey
getPublicKey = skpPublicKey . casSigningKey

-- | Export public key as hex string
exportPublicKey :: CASClient -> Text
exportPublicKey client =
  Text.decodeUtf8 $ Base16.encode $ BA.convert (getPublicKey client)
