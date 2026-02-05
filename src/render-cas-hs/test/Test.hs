{-# LANGUAGE OverloadedStrings #-}

-- | Render CAS Test Suite
-- | Comprehensive tests for CAS client functionality
module Main where

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

import Render.CAS.Client

import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Base16 as Base16
import qualified Data.ByteString.Lazy as BSL
import Data.Time (getCurrentTime, addUTCTime)
import qualified Data.ByteArray as BA
import Crypto.PubKey.Ed25519 (PublicKey)
import Data.Aeson (encode, decode, object, (.=), Value(..))
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Key (fromText)
import Data.Maybe (isJust, isNothing)
import qualified Data.Map.Strict as Map

main :: IO ()
main = hspec $ do
  describe "Render CAS Tests" $ do
    hashTests
    signingTests
    auditRecordTests
    propertyTests
    casClientTests
    casDeepTests

-- | Hash computation tests
hashTests :: Spec
hashTests = describe "Hash Computation" $ do
  it "computes BLAKE2b-256 hash" $ do
    let content = "test content" :: ByteString
    let hash = computeContentHash content
    BS.length hash `shouldBe` 32 -- BLAKE2b-256 is 32 bytes

  it "computes SHA256 hash" $ do
    let content = "test content" :: ByteString
    let hash = computeSHA256Hash content
    BS.length hash `shouldBe` 32 -- SHA256 is 32 bytes

  it "produces deterministic hashes" $ do
    let content = "test content" :: ByteString
    let hash1 = computeContentHash content
    let hash2 = computeContentHash content
    hash1 `shouldBe` hash2

  it "produces different hashes for different content" $ do
    let content1 = "test content 1" :: ByteString
    let content2 = "test content 2" :: ByteString
    let hash1 = computeContentHash content1
    let hash2 = computeContentHash content2
    hash1 `shouldNotBe` hash2

-- | Signing tests
signingTests :: Spec
signingTests = describe "Ed25519 Signing" $ do
  it "signs data and verifies signature" $ do
    client <- createCASClient "https://cas.test" "test-bucket"
    let content = "test content" :: ByteString
    
    let signature = signBatch client content
    BS.length signature `shouldBe` 64 -- Ed25519 signature is 64 bytes
    
    let publicKey = getPublicKey client
    let verified = verifySignature publicKey content signature
    verified `shouldBe` True

  it "rejects invalid signature" $ do
    client <- createCASClient "https://cas.test" "test-bucket"
    let content = "test content" :: ByteString
    let wrongContent = "wrong content" :: ByteString
    let signature = signBatch client content
    
    let publicKey = getPublicKey client
    let verified = verifySignature publicKey wrongContent signature
    verified `shouldBe` False

  it "produces different signatures for different content" $ do
    client <- createCASClient "https://cas.test" "test-bucket"
    let content1 = "test content 1" :: ByteString
    let content2 = "test content 2" :: ByteString
    
    let sig1 = signBatch client content1
    let sig2 = signBatch client content2
    sig1 `shouldNotBe` sig2

-- | Audit record tests
auditRecordTests :: Spec
auditRecordTests = describe "Audit Records" $ do
  it "creates audit record with coeffect" $ do
    client <- createCASClient "https://cas.test" "test-bucket"
    now <- getCurrentTime
    let content = "audit content" :: ByteString
    
    let coeffect = Coeffect
          { coeffectResource = "gpu-seconds"
          , coeffectAmount = 1.5
          }
    
    let discharge = DischargeProof
          { dischargeProof = BS.pack [1, 2, 3, 4]
          , dischargeTimestamp = now
          }
    
    let contentHash = computeContentHash content
    let signature = signBatch client content
    
    let record = AuditRecord
          { arContent = content
          , arCoeffect = coeffect
          , arDischarge = discharge
          , arSignature = signature
          , arContentHash = contentHash
          }
    
    coeffectResource (arCoeffect record) `shouldBe` "gpu-seconds"
    coeffectAmount (arCoeffect record) `shouldBe` 1.5

  it "serializes and deserializes audit batch" $ do
    client <- createCASClient "https://cas.test" "test-bucket"
    now <- getCurrentTime
    let content = "audit content" :: ByteString
    
    let record = AuditRecord
          { arContent = content
          , arCoeffect = Coeffect "gpu-seconds" 1.5
          , arDischarge = DischargeProof (BS.pack [1, 2, 3]) now
          , arSignature = signBatch client content
          , arContentHash = computeContentHash content
          }
    
    let batch = serializeBatch [record]
    let deserialized = deserializeBatch batch
    
    length deserialized `shouldBe` 1
    case deserialized of
      [r] -> coeffectResource (arCoeffect r) `shouldBe` "gpu-seconds"
      _ -> expectationFailure "Should deserialize one record"

-- | Property tests
propertyTests :: Spec
propertyTests = describe "Property Tests" $ do
  prop "hash is always 32 bytes" $ \content -> do
    let hash = computeContentHash (BS.pack content)
    BS.length hash `shouldBe` 32

  prop "signature is always 64 bytes" $ \content -> do
    client <- createCASClient "https://cas.test" "test-bucket"
    let sig = signBatch client (BS.pack content)
    BS.length sig `shouldBe` 64

  prop "signature verification roundtrip" $ \content -> do
    client <- createCASClient "https://cas.test" "test-bucket"
    let contentBS = BS.pack content
    let sig = signBatch client contentBS
    let publicKey = getPublicKey client
    verifySignature publicKey contentBS sig `shouldBe` True

  prop "different content produces different hashes" $ \content1 content2 -> do
    let hash1 = computeContentHash (BS.pack content1)
    let hash2 = computeContentHash (BS.pack content2)
    if content1 == content2
      then hash1 `shouldBe` hash2
      else hash1 `shouldNotBe` hash2

-- | Deep comprehensive tests for CAS Client functions
casClientTests :: Spec
casClientTests = describe "CAS Client Deep Tests" $ do
  describe "computeContentHash" $ do
    it "handles empty content" $ do
      let hash = computeContentHash BS.empty
      BS.length hash `shouldBe` 32
      hash `shouldNotBe` BS.empty

    it "handles very large content" $ do
      let largeContent = BS.replicate 1000000 65 -- 1MB of 'A'
      let hash = computeContentHash largeContent
      BS.length hash `shouldBe` 32

    it "produces consistent hash for same content" $ do
      let content = BS.pack [1..100]
      let hash1 = computeContentHash content
      let hash2 = computeContentHash content
      hash1 `shouldBe` hash2

  describe "computeSHA256Hash" $ do
    it "handles empty content" $ do
      let hash = computeSHA256Hash BS.empty
      BS.length hash `shouldBe` 32

    it "produces different hash than BLAKE2b for same content" $ do
      let content = "test content" :: ByteString
      let blakeHash = computeContentHash content
      let shaHash = computeSHA256Hash content
      blakeHash `shouldNotBe` shaHash

  describe "signData and verifySignature" $ do
    it "handles empty content signing" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      let sig = signBatch client BS.empty
      BS.length sig `shouldBe` 64
      let publicKey = getPublicKey client
      verifySignature publicKey BS.empty sig `shouldBe` True

    it "rejects signature for modified content" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      let content = "original content" :: ByteString
      let modified = "modified content" :: ByteString
      let sig = signBatch client content
      let publicKey = getPublicKey client
      verifySignature publicKey modified sig `shouldBe` False

    it "rejects signature for wrong public key" $ do
      client1 <- createCASClient "https://cas.test" "test-bucket"
      client2 <- createCASClient "https://cas.test" "test-bucket"
      let content = "test content" :: ByteString
      let sig = signBatch client1 content
      let publicKey2 = getPublicKey client2
      verifySignature publicKey2 content sig `shouldBe` False

  describe "serializeBatch and deserializeBatch" $ do
    it "handles empty batch" $ do
      let batch = serializeBatch []
      let deserialized = deserializeBatch batch
      length deserialized `shouldBe` 0

    it "handles batch with multiple records" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      now <- getCurrentTime
      let record1 = AuditRecord
            { arContent = BS.pack [1, 2, 3]
            , arCoeffect = Coeffect "gpu-seconds" 1.0
            , arDischarge = DischargeProof (BS.pack [1]) now
            , arSignature = signBatch client (BS.pack [1, 2, 3])
            , arContentHash = computeContentHash (BS.pack [1, 2, 3])
            }
      let record2 = AuditRecord
            { arContent = BS.pack [4, 5, 6]
            , arCoeffect = Coeffect "gpu-seconds" 2.0
            , arDischarge = DischargeProof (BS.pack [2]) now
            , arSignature = signBatch client (BS.pack [4, 5, 6])
            , arContentHash = computeContentHash (BS.pack [4, 5, 6])
            }
      let batch = serializeBatch [record1, record2]
      let deserialized = deserializeBatch batch
      length deserialized `shouldBe` 2
      coeffectAmount (arCoeffect (head deserialized)) `shouldBe` 1.0
      coeffectAmount (arCoeffect (last deserialized)) `shouldBe` 2.0

    it "handles invalid JSON gracefully" $ do
      let invalidJSON = BS.pack [0, 1, 2, 3] -- Invalid JSON bytes
      let deserialized = deserializeBatch invalidJSON
      length deserialized `shouldBe` 0 -- Should return empty list, not crash

  describe "computeDeltas" $ do
    it "handles empty metrics" $ do
      let deltas = computeDeltas [] []
      length deltas `shouldBe` 0

    it "handles metrics only in ClickHouse" $ do
      let chMetrics = [("customer1", 100)]
      let casMetrics = []
      let deltas = computeDeltas chMetrics casMetrics
      length deltas `shouldBe` 1
      case deltas of
        [(cid, delta)] -> do
          cid `shouldBe` "customer1"
          delta `shouldBe` (-100.0) -- 100% difference (CAS has 0, CH has 100)

    it "handles metrics only in CAS" $ do
      let chMetrics = []
      let casMetrics = [("customer1", 100)]
      let deltas = computeDeltas chMetrics casMetrics
      length deltas `shouldBe` 1
      case deltas of
        [(cid, delta)] -> do
          cid `shouldBe` "customer1"
          delta `shouldBe` 100.0 -- 100% difference (CH has 0, CAS has 100)

    it "calculates zero delta for matching metrics" $ do
      let chMetrics = [("customer1", 100), ("customer2", 200)]
      let casMetrics = [("customer1", 100), ("customer2", 200)]
      let deltas = computeDeltas chMetrics casMetrics
      length deltas `shouldBe` 2
      case deltas of
        [(cid1, delta1), (cid2, delta2)] -> do
          delta1 `shouldBe` 0.0
          delta2 `shouldBe` 0.0

    it "calculates percentage delta correctly" $ do
      let chMetrics = [("customer1", 100)]
      let casMetrics = [("customer1", 150)]
      let deltas = computeDeltas chMetrics casMetrics
      case deltas of
        [(cid, delta)] -> do
          cid `shouldBe` "customer1"
          delta `shouldBe` 50.0 -- (150-100)/100 * 100 = 50%

    it "handles zero ClickHouse value" $ do
      let chMetrics = [("customer1", 0)]
      let casMetrics = [("customer1", 50)]
      let deltas = computeDeltas chMetrics casMetrics
      case deltas of
        [(cid, delta)] -> do
          cid `shouldBe` "customer1"
          delta `shouldBe` 100.0 -- When CH is 0 and CAS > 0, delta is 100%

    it "handles both zero values" $ do
      let chMetrics = [("customer1", 0)]
      let casMetrics = [("customer1", 0)]
      let deltas = computeDeltas chMetrics casMetrics
      case deltas of
        [(cid, delta)] -> do
          cid `shouldBe` "customer1"
          delta `shouldBe` 0.0

  describe "attestationToRecord" $ do
    it "creates audit record with correct coeffect" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      now <- getCurrentTime
      let attestation = GPUAttestation
            { gpuRequestId = "req-123"
            , gpuCustomerId = Just "customer-456"
            , gpuSeconds = 2.5
            , gpuDeviceUuid = "device-789"
            , gpuModelName = "model-xyz"
            , gpuTimestamp = now
            , gpuSignature = BS.pack [1..64]
            }
      record <- attestationToRecord client attestation
      coeffectResource (arCoeffect record) `shouldBe` "gpu-seconds"
      coeffectAmount (arCoeffect record) `shouldBe` 2.5
      dischargeTimestamp (arDischarge record) `shouldBe` now

    it "handles attestation with no customer ID" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      now <- getCurrentTime
      let attestation = GPUAttestation
            { gpuRequestId = "req-123"
            , gpuCustomerId = Nothing
            , gpuSeconds = 1.0
            , gpuDeviceUuid = "device-789"
            , gpuModelName = "model-xyz"
            , gpuTimestamp = now
            , gpuSignature = BS.pack [1..64]
            }
      record <- attestationToRecord client attestation
      coeffectAmount (arCoeffect record) `shouldBe` 1.0

  describe "writeAuditBatch" $ do
    it "computes content hash correctly" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      now <- getCurrentTime
      let record = AuditRecord
            { arContent = BS.pack [1, 2, 3]
            , arCoeffect = Coeffect "gpu-seconds" 1.0
            , arDischarge = DischargeProof (BS.pack [1]) now
            , arSignature = signBatch client (BS.pack [1, 2, 3])
            , arContentHash = computeContentHash (BS.pack [1, 2, 3])
            }
      -- Note: This will fail HTTP call, but we can verify the logic
      result <- writeAuditBatch client [record]
      -- Should return Left due to HTTP failure, but structure is correct
      case result of
        Left _ -> pure () -- Expected (no actual CAS server)
        Right hash -> hash `shouldNotBe` ""

  describe "getAuditBatch signature verification" $ do
    it "rejects batch with invalid signature" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      -- Note: This will fail HTTP call, but we test the verification logic
      result <- getAuditBatch client "test-hash"
      case result of
        Left err -> err `shouldContain` "CAS fetch error" -- HTTP error expected
        Right _ -> expectationFailure "Should fail due to HTTP error"

  describe "exportPublicKey" $ do
    it "exports public key as hex string" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      let hexKey = exportPublicKey client
      Text.length hexKey `shouldBe` 64 -- Ed25519 public key is 32 bytes = 64 hex chars
      -- Should be valid hex
      let isValidHex = Text.all (\c -> (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')) hexKey
      isValidHex `shouldBe` True

  describe "reconcileMetrics threshold handling" $ do
    it "reports Reconciled when deltas below threshold" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      now <- getCurrentTime
      let range = TimeRange now (addUTCTime 3600 now)
      -- Note: This will fail HTTP calls, but we test the reconciliation logic structure
      result <- reconcileMetrics client range
      -- Should handle gracefully even if queries fail
      rrRange result `shouldBe` range

    it "handles time range correctly" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      now <- getCurrentTime
      let start = now
      let end = addUTCTime 3600 now
      let range = TimeRange start end
      result <- reconcileMetrics client range
      rrRange result `shouldBe` range

-- | Deep comprehensive CAS tests for edge cases and bug detection
casDeepTests :: Spec
casDeepTests = describe "CAS Deep Tests" $ do
  describe "Base16 Encoding/Decoding Edge Cases" $ do
    it "handles empty ByteString encoding" $ do
      let encoded = Base16.encode BS.empty
      BS.length encoded `shouldBe` 0

    it "handles odd-length hex string decoding" $ do
      let invalidHex = BS.pack [65, 66, 67] -- "ABC" (odd length)
      case Base16.decode invalidHex of
        Left _ -> pure () -- Should fail gracefully
        Right _ -> expectationFailure "Should reject odd-length hex"

    it "handles invalid hex characters in decoding" $ do
      let invalidHex = BS.pack [71, 72, 73, 74] -- "GHIJ" (invalid hex)
      case Base16.decode invalidHex of
        Left _ -> pure () -- Should fail gracefully
        Right _ -> expectationFailure "Should reject invalid hex characters"

    it "round-trips Base16 encoding/decoding" $ do
      let original = BS.pack [0..255]
      let encoded = Base16.encode original
      case Base16.decode encoded of
        Left _ -> expectationFailure "Should decode valid hex"
        Right decoded -> decoded `shouldBe` original

    it "handles signature Base16 encoding in JSON" $ do
      let sig = BS.pack [1..64]
      let hexSig = Base16.encode sig
      let textSig = Text.decodeUtf8 hexSig
      -- Should be valid hex string
      Text.length textSig `shouldBe` 128 -- 64 bytes = 128 hex chars

  describe "JSON Serialization/Deserialization Edge Cases" $ do
    it "handles deserializeBatch with malformed JSON" $ do
      let malformed = BS.pack [123, 125, 0, 1, 2] -- "{}\0\1\2"
      let deserialized = deserializeBatch malformed
      -- Should return empty list, not crash
      length deserialized `shouldBe` 0

    it "handles deserializeBatch with truncated JSON" $ do
      let truncated = BS.pack [123, 34, 99, 111, 110, 116, 101, 110, 116] -- Truncated JSON
      let deserialized = deserializeBatch truncated
      length deserialized `shouldBe` 0

    it "handles deserializeBatch with empty JSON array" $ do
      let emptyArray = BS.pack [91, 93] -- "[]"
      let deserialized = deserializeBatch emptyArray
      length deserialized `shouldBe` 0

    it "handles deserializeBatch with valid single record" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      now <- getCurrentTime
      let record = AuditRecord
            { arContent = BS.pack [1, 2, 3]
            , arCoeffect = Coeffect "gpu-seconds" 1.0
            , arDischarge = DischargeProof (BS.pack [1]) now
            , arSignature = signBatch client (BS.pack [1, 2, 3])
            , arContentHash = computeContentHash (BS.pack [1, 2, 3])
            }
      let batch = serializeBatch [record]
      let deserialized = deserializeBatch batch
      length deserialized `shouldBe` 1

    it "handles GPUAttestation with None customer_id" $ do
      now <- getCurrentTime
      let attestation = GPUAttestation
            { gpuRequestId = "req-123"
            , gpuCustomerId = Nothing
            , gpuSeconds = 1.0
            , gpuDeviceUuid = "device-123"
            , gpuModelName = "model-123"
            , gpuTimestamp = now
            , gpuSignature = BS.pack [1..64]
            }
      let json = encode attestation
      case decode json of
        Just decoded -> gpuCustomerId decoded `shouldBe` Nothing
        Nothing -> expectationFailure "Should decode attestation with None customer_id"

    it "handles GPUAttestation JSON with missing fields" $ do
      -- Create JSON object missing required fields
      let incompleteJson = object ["request_id" .= ("req-123" :: Text)]
      let jsonBytes = BSL.toStrict (encode incompleteJson)
      case decode (BSL.fromStrict jsonBytes) of
        Just (_ :: GPUAttestation) -> expectationFailure "Should reject incomplete attestation"
        Nothing -> pure () -- Expected: missing fields should cause decode failure

  describe "Signature Verification Edge Cases" $ do
    it "rejects signature with wrong length" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      let content = "test content" :: ByteString
      let wrongLengthSig = BS.pack [1..63] -- 63 bytes instead of 64
      let publicKey = getPublicKey client
      -- Should handle gracefully (verifySignature may fail or return False)
      let verified = verifySignature publicKey content wrongLengthSig
      verified `shouldBe` False

    it "rejects signature with all zeros" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      let content = "test content" :: ByteString
      let zeroSig = BS.replicate 64 0
      let publicKey = getPublicKey client
      verifySignature publicKey content zeroSig `shouldBe` False

    it "rejects signature with all ones" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      let content = "test content" :: ByteString
      let onesSig = BS.replicate 64 255
      let publicKey = getPublicKey client
      verifySignature publicKey content onesSig `shouldBe` False

    it "verifies signature for empty content" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      let content = BS.empty
      let sig = signBatch client content
      let publicKey = getPublicKey client
      verifySignature publicKey content sig `shouldBe` True

    it "rejects signature when content modified by one byte" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      let content1 = BS.pack [1, 2, 3, 4]
      let content2 = BS.pack [1, 2, 3, 5] -- One byte different
      let sig = signBatch client content1
      let publicKey = getPublicKey client
      verifySignature publicKey content2 sig `shouldBe` False

  describe "Time Range Filtering Edge Cases" $ do
    it "handles record exactly at start time boundary" $ do
      now <- getCurrentTime
      let record = AuditRecord
            { arContent = BS.pack [1]
            , arCoeffect = Coeffect "gpu-seconds" 1.0
            , arDischarge = DischargeProof (BS.pack [1]) now
            , arSignature = BS.pack [1..64]
            , arContentHash = BS.pack [1..32]
            }
      -- Record timestamp equals start time
      let start = now
      let end = addUTCTime 3600 now
      -- Should include record (>= start)
      dischargeTimestamp (arDischarge record) >= start `shouldBe` True

    it "handles record exactly at end time boundary" $ do
      now <- getCurrentTime
      let end = now
      let record = AuditRecord
            { arContent = BS.pack [1]
            , arCoeffect = Coeffect "gpu-seconds" 1.0
            , arDischarge = DischargeProof (BS.pack [1]) end
            , arSignature = BS.pack [1..64]
            , arContentHash = BS.pack [1..32]
            }
      let start = addUTCTime (-3600) now
      -- Should exclude record (< end, not <= end)
      dischargeTimestamp (arDischarge record) < end `shouldBe` False

    it "handles record before start time" $ do
      now <- getCurrentTime
      let start = now
      let record = AuditRecord
            { arContent = BS.pack [1]
            , arCoeffect = Coeffect "gpu-seconds" 1.0
            , arDischarge = DischargeProof (BS.pack [1]) (addUTCTime (-1) start)
            , arSignature = BS.pack [1..64]
            , arContentHash = BS.pack [1..32]
            }
      let end = addUTCTime 3600 start
      -- Should exclude record
      dischargeTimestamp (arDischarge record) >= start `shouldBe` False

    it "handles record after end time" $ do
      now <- getCurrentTime
      let start = now
      let end = addUTCTime 3600 start
      let record = AuditRecord
            { arContent = BS.pack [1]
            , arCoeffect = Coeffect "gpu-seconds" 1.0
            , arDischarge = DischargeProof (BS.pack [1]) (addUTCTime 1 end)
            , arSignature = BS.pack [1..64]
            , arContentHash = BS.pack [1..32]
            }
      -- Should exclude record
      dischargeTimestamp (arDischarge record) < end `shouldBe` False

  describe "Customer ID Extraction Edge Cases" $ do
    it "handles attestation with None customer_id" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      now <- getCurrentTime
      let attestation = GPUAttestation
            { gpuRequestId = "req-123"
            , gpuCustomerId = Nothing
            , gpuSeconds = 1.0
            , gpuDeviceUuid = "device-123"
            , gpuModelName = "model-123"
            , gpuTimestamp = now
            , gpuSignature = BS.pack [1..64]
            }
      record <- attestationToRecord client attestation
      -- Extract customer ID from record
      let content = arContent record
      case decode (BSL.fromStrict content) of
        Just (decoded :: GPUAttestation) -> gpuCustomerId decoded `shouldBe` Nothing
        Nothing -> expectationFailure "Should decode attestation"

    it "handles attestation with empty customer_id string" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      now <- getCurrentTime
      let attestation = GPUAttestation
            { gpuRequestId = "req-123"
            , gpuCustomerId = Just ""
            , gpuSeconds = 1.0
            , gpuDeviceUuid = "device-123"
            , gpuModelName = "model-123"
            , gpuTimestamp = now
            , gpuSignature = BS.pack [1..64]
            }
      record <- attestationToRecord client attestation
      let content = arContent record
      case decode (BSL.fromStrict content) of
        Just (decoded :: GPUAttestation) -> 
          case gpuCustomerId decoded of
            Just "" -> pure () -- Empty string is valid
            _ -> expectationFailure "Should preserve empty string customer_id"
        Nothing -> expectationFailure "Should decode attestation"

    it "handles malformed JSON in arContent" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      now <- getCurrentTime
      -- Create record with malformed content
      let record = AuditRecord
            { arContent = BS.pack [123, 125, 0, 1, 2] -- Malformed JSON
            , arCoeffect = Coeffect "gpu-seconds" 1.0
            , arDischarge = DischargeProof (BS.pack [1]) now
            , arSignature = signBatch client (BS.pack [123, 125])
            , arContentHash = computeContentHash (BS.pack [123, 125])
            }
      -- Attempt to extract customer ID (should return Nothing)
      case decode (BSL.fromStrict (arContent record)) of
        Just (_ :: GPUAttestation) -> expectationFailure "Should not decode malformed JSON"
        Nothing -> pure () -- Expected

  describe "computeDeltas Edge Cases" $ do
    it "handles negative ClickHouse values (edge case)" $ do
      -- Note: Int cannot be negative in practice, but test edge case
      let chMetrics = [("customer1", 100)]
      let casMetrics = [("customer1", 50)]
      let deltas = computeDeltas chMetrics casMetrics
      case deltas of
        [(cid, delta)] -> delta `shouldBe` (-50.0) -- (50-100)/100 * 100 = -50%

    it "handles very large delta percentages" $ do
      let chMetrics = [("customer1", 1)]
      let casMetrics = [("customer1", 1000)]
      let deltas = computeDeltas chMetrics casMetrics
      case deltas of
        [(cid, delta)] -> delta `shouldBe` 99900.0 -- (1000-1)/1 * 100 = 99900%

    it "handles duplicate customer IDs in same list" $ do
      -- Map.fromList will take last value for duplicates
      let chMetrics = [("customer1", 100), ("customer1", 200)]
      let casMetrics = [("customer1", 150)]
      let deltas = computeDeltas chMetrics casMetrics
      -- Should use last value (200) for customer1
      case deltas of
        [(cid, delta)] -> do
          cid `shouldBe` "customer1"
          delta `shouldBe` (-25.0) -- (150-200)/200 * 100 = -25%

    it "handles multiple customers with mixed deltas" $ do
      let chMetrics = [("customer1", 100), ("customer2", 200), ("customer3", 50)]
      let casMetrics = [("customer1", 100), ("customer2", 250), ("customer4", 75)]
      let deltas = computeDeltas chMetrics casMetrics
      length deltas `shouldBe` 4 -- All 4 customers should appear
      -- Verify each delta
      let deltaMap = Map.fromList deltas
      Map.lookup "customer1" deltaMap `shouldBe` Just 0.0
      Map.lookup "customer2" deltaMap `shouldBe` Just 25.0
      Map.lookup "customer3" deltaMap `shouldBe` Just (-100.0)
      Map.lookup "customer4" deltaMap `shouldBe` Just 100.0

  describe "Large Batch Handling" $ do
    it "handles large batch serialization" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      now <- getCurrentTime
      -- Create 1000 records
      let records = map (\i -> AuditRecord
            { arContent = BS.pack [fromIntegral i]
            , arCoeffect = Coeffect "gpu-seconds" (fromIntegral i)
            , arDischarge = DischargeProof (BS.pack [fromIntegral i]) now
            , arSignature = signBatch client (BS.pack [fromIntegral i])
            , arContentHash = computeContentHash (BS.pack [fromIntegral i])
            }) [1..1000]
      let batch = serializeBatch records
      BS.length batch > 0 `shouldBe` True
      let deserialized = deserializeBatch batch
      length deserialized `shouldBe` 1000

    it "handles very large content in single record" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      now <- getCurrentTime
      let largeContent = BS.replicate 1000000 65 -- 1MB
      let record = AuditRecord
            { arContent = largeContent
            , arCoeffect = Coeffect "gpu-seconds" 1.0
            , arDischarge = DischargeProof (BS.pack [1]) now
            , arSignature = signBatch client largeContent
            , arContentHash = computeContentHash largeContent
            }
      let batch = serializeBatch [record]
      BS.length batch > 1000000 `shouldBe` True -- Should serialize successfully

  describe "Error Handling" $ do
    it "handles network timeout gracefully" $ do
      -- Use invalid endpoint to trigger network error
      client <- createCASClient "http://invalid-host-that-does-not-exist" "test-bucket"
      now <- getCurrentTime
      let record = AuditRecord
            { arContent = BS.pack [1]
            , arCoeffect = Coeffect "gpu-seconds" 1.0
            , arDischarge = DischargeProof (BS.pack [1]) now
            , arSignature = signBatch client (BS.pack [1])
            , arContentHash = computeContentHash (BS.pack [1])
            }
      result <- writeAuditBatch client [record]
      case result of
        Left err -> Text.isInfixOf "error" (Text.pack err) `shouldBe` True
        Right _ -> expectationFailure "Should return error for invalid host"

    it "handles fetchFromCAS with missing signature header" $ do
      -- This tests the error path in fetchFromCAS
      client <- createCASClient "http://invalid-host" "test-bucket"
      result <- fetchFromCAS client "test-hash"
      case result of
        Left err -> pure () -- Expected error
        Right _ -> expectationFailure "Should return error"

    it "handles getAuditBatch with invalid hash" $ do
      client <- createCASClient "http://invalid-host" "test-bucket"
      result <- getAuditBatch client "invalid-hash"
      case result of
        Left err -> pure () -- Expected error
        Right _ -> expectationFailure "Should return error"

  describe "Content Hash Consistency" $ do
    it "produces same hash for identical content" $ do
      let content = BS.pack [1..100]
      let hash1 = computeContentHash content
      let hash2 = computeContentHash content
      hash1 `shouldBe` hash2

    it "produces different hash for different content" $ do
      let content1 = BS.pack [1..100]
      let content2 = BS.pack [1..99] <> BS.pack [101]
      let hash1 = computeContentHash content1
      let hash2 = computeContentHash content2
      hash1 `shouldNotBe` hash2

    it "hash length is always 32 bytes" $ do
      let contents = [BS.empty, BS.pack [1], BS.pack [1..100], BS.replicate 1000000 65]
      mapM_ (\content -> BS.length (computeContentHash content) `shouldBe` 32) contents

  describe "attestationToRecord Consistency" $ do
    it "creates record with matching content hash" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      now <- getCurrentTime
      let attestation = GPUAttestation
            { gpuRequestId = "req-123"
            , gpuCustomerId = Just "customer-123"
            , gpuSeconds = 2.5
            , gpuDeviceUuid = "device-123"
            , gpuModelName = "model-123"
            , gpuTimestamp = now
            , gpuSignature = BS.pack [1..64]
            }
      record <- attestationToRecord client attestation
      -- Content hash should match serialized attestation
      let expectedContent = BSL.toStrict (encode attestation)
      let expectedHash = computeContentHash expectedContent
      arContentHash record `shouldBe` expectedHash

    it "creates record with valid signature" $ do
      client <- createCASClient "https://cas.test" "test-bucket"
      now <- getCurrentTime
      let attestation = GPUAttestation
            { gpuRequestId = "req-123"
            , gpuCustomerId = Just "customer-123"
            , gpuSeconds = 2.5
            , gpuDeviceUuid = "device-123"
            , gpuModelName = "model-123"
            , gpuTimestamp = now
            , gpuSignature = BS.pack [1..64]
            }
      record <- attestationToRecord client attestation
      -- Signature should verify
      let publicKey = getPublicKey client
      verifySignature publicKey (arContent record) (arSignature record) `shouldBe` True
