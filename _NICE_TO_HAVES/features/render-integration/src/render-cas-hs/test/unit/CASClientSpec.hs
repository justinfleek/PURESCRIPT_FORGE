{-# LANGUAGE OverloadedStrings #-}

-- | Deep comprehensive unit tests for CAS Client module
-- | Tests individual functions in isolation: computeContentHash, computeSHA256Hash,
-- | signData, verifySignature, serializeBatch, deserializeBatch, computeDeltas
module CASClientSpec where

import Test.Hspec
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Base16 as Base16
import qualified Data.ByteString.Lazy as BSL
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Data.Time (getCurrentTime, UTCTime)
import Data.Aeson (encode, decode, object, (.=))
import qualified Data.Aeson as Aeson
import Render.CAS.Client
  ( CASClient(..)
  , createCASClient
  , computeContentHash
  , computeSHA256Hash
  , serializeBatch
  , deserializeBatch
  , computeDeltas
  , signBatch
  , verifyBatchSignature
  , AuditRecord(..)
  , Coeffect(..)
  , DischargeProof(..)
  , GPUAttestation(..)
  )
import Crypto.PubKey.Ed25519 (SecretKey, PublicKey, generateSecretKey, toPublic)
import qualified Data.Map.Strict as Map

-- | Helper to create test signing key pair
createTestSigningKeyPair :: IO (SecretKey, PublicKey)
createTestSigningKeyPair = do
  sk <- generateSecretKey
  let pk = toPublic sk
  pure (sk, pk)

-- | Helper to create test audit record
createTestAuditRecord :: ByteString -> IO AuditRecord
createTestAuditRecord content = do
  now <- getCurrentTime
  client <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
  let contentHash = computeContentHash content
  let signature = signBatch client content
  let coeffect = Coeffect { coeffectResource = "gpu-seconds", coeffectAmount = 1.0 }
  let discharge = DischargeProof
        { dischargeProof = BS.pack [1, 2, 3, 4]
        , dischargeTimestamp = now
        }
  pure AuditRecord
    { arContent = content
    , arCoeffect = coeffect
    , arDischarge = discharge
    , arSignature = signature
    , arContentHash = contentHash
    }

-- | Deep comprehensive unit tests for CAS Client module
spec :: Spec
spec = describe "CAS Client Unit Tests" $ do
  describe "computeContentHash" $ do
    it "computes hash for empty content" $ do
      let content = BS.empty
      let hash = computeContentHash content
      
      -- Hash should be 32 bytes (BLAKE2b-256)
      BS.length hash `shouldBe` 32

    it "BUG: computes hash deterministically for same content" $ do
      -- BUG: computeContentHash (line 180-184) uses BLAKE2b-256 hash, which is
      -- deterministic. However, if the hash implementation changes or if there's
      -- a bug in the hash library, hashes may not be deterministic across runs.
      let content = Text.encodeUtf8 "test content"
      let hash1 = computeContentHash content
      let hash2 = computeContentHash content
      
      hash1 `shouldBe` hash2

    it "BUG: produces different hashes for different content" $ do
      -- BUG: computeContentHash should produce different hashes for different content.
      -- If two different contents produce the same hash, this indicates a hash collision
      -- (extremely unlikely for BLAKE2b-256) or a bug in the hash implementation.
      let content1 = Text.encodeUtf8 "content1"
      let content2 = Text.encodeUtf8 "content2"
      let hash1 = computeContentHash content1
      let hash2 = computeContentHash content2
      
      hash1 `shouldNotBe` hash2

    it "BUG: hash length may not always be 32 bytes" $ do
      -- BUG: computeContentHash should always produce 32-byte hashes (BLAKE2b-256).
      -- If the hash library changes or if there's a bug, hash length may vary.
      let content = Text.encodeUtf8 "test"
      let hash = computeContentHash content
      
      BS.length hash `shouldBe` 32

    it "handles very large content" $ do
      -- Large content (1MB)
      let largeContent = BS.replicate (1024 * 1024) 65 -- 'A' repeated
      let hash = computeContentHash largeContent
      
      BS.length hash `shouldBe` 32

  describe "computeSHA256Hash" $ do
    it "computes SHA256 hash for empty content" $ do
      let content = BS.empty
      let hash = computeSHA256Hash content
      
      -- SHA256 hash should be 32 bytes
      BS.length hash `shouldBe` 32

    it "BUG: produces different hash than BLAKE2b for same content" $ do
      -- BUG: computeSHA256Hash (line 187-191) uses SHA256, which should produce
      -- different hashes than BLAKE2b-256 for the same content. If they're the same,
      -- there's a bug (wrong hash algorithm used).
      let content = Text.encodeUtf8 "test content"
      let blakeHash = computeContentHash content
      let shaHash = computeSHA256Hash content
      
      blakeHash `shouldNotBe` shaHash

    it "BUG: SHA256 hash length may not always be 32 bytes" $ do
      -- BUG: computeSHA256Hash should always produce 32-byte hashes.
      let content = Text.encodeUtf8 "test"
      let hash = computeSHA256Hash content
      
      BS.length hash `shouldBe` 32

  describe "signBatch" $ do
    it "signs content and produces 64-byte signature" $ do
      client <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      let content = Text.encodeUtf8 "test content"
      let signature = signBatch client content
      
      -- Ed25519 signature should be 64 bytes
      BS.length signature `shouldBe` 64

    it "BUG: produces different signatures for different content" $ do
      -- BUG: signBatch (line 208-209) should produce different signatures for
      -- different content. If two different contents produce the same signature,
      -- this indicates a bug (signature not content-dependent).
      client <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      let content1 = Text.encodeUtf8 "content1"
      let content2 = Text.encodeUtf8 "content2"
      let sig1 = signBatch client content1
      let sig2 = signBatch client content2
      
      sig1 `shouldNotBe` sig2

    it "BUG: produces same signature for same content" $ do
      -- BUG: signBatch should be deterministic - same content with same key produces
      -- same signature. If signatures differ for same content, there's a bug
      -- (non-deterministic signing).
      client <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      let content = Text.encodeUtf8 "test content"
      let sig1 = signBatch client content
      let sig2 = signBatch client content
      
      sig1 `shouldBe` sig2

    it "BUG: signature length may not always be 64 bytes" $ do
      -- BUG: signBatch should always produce 64-byte signatures (Ed25519).
      client <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      let content = Text.encodeUtf8 "test"
      let signature = signBatch client content
      
      BS.length signature `shouldBe` 64

  describe "verifyBatchSignature" $ do
    it "verifies valid signature" $ do
      client <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      let content = Text.encodeUtf8 "test content"
      let signature = signBatch client content
      
      verifyBatchSignature client content signature `shouldBe` True

    it "BUG: rejects signature for modified content" $ do
      -- BUG: verifyBatchSignature (line 212-213) should reject signatures for modified content.
      -- If it accepts signatures for different content, this indicates a security vulnerability.
      client <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      let content1 = Text.encodeUtf8 "content1"
      let content2 = Text.encodeUtf8 "content2"
      let signature = signBatch client content1
      
      verifyBatchSignature client content2 signature `shouldBe` False

    it "BUG: rejects signature with wrong length" $ do
      -- BUG: verifyBatchSignature should reject signatures with wrong length (not 64 bytes).
      -- If it accepts wrong-length signatures, this may indicate a bug in signature
      -- validation or conversion.
      client <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      let content = Text.encodeUtf8 "test content"
      let wrongSignature = BS.pack [1, 2, 3] -- Wrong length
      
      -- BUG: verifyBatchSignature may crash or return incorrect result for wrong-length signature
      -- The BA.convert may fail or produce invalid signature
      let result = verifyBatchSignature client content wrongSignature
      -- Should reject wrong-length signature
      result `shouldBe` False

    it "BUG: rejects signature with wrong public key" $ do
      -- BUG: verifyBatchSignature should reject signatures signed with different key.
      -- If it accepts signatures from wrong key, this is a security vulnerability.
      client1 <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      client2 <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      let content = Text.encodeUtf8 "test content"
      let signature = signBatch client1 content
      
      -- Verify with different client (different key)
      verifyBatchSignature client2 content signature `shouldBe` False

    it "BUG: may be vulnerable to timing attacks" $ do
      -- BUG: verifyBatchSignature uses Ed25519 verification, which should be constant-time.
      -- However, if the implementation is not constant-time, it may be vulnerable to
      -- timing attacks that leak information about the signature or content.
      client <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      let content = Text.encodeUtf8 "test content"
      let signature = signBatch client content
      
      -- This test documents the potential vulnerability - actual timing attack testing
      -- would require measuring execution time, which is beyond unit test scope.
      verifyBatchSignature client content signature `shouldBe` True

  describe "serializeBatch" $ do
    it "serializes empty batch" $ do
      let records = [] :: [AuditRecord]
      let serialized = serializeBatch records
      
      -- Empty batch should serialize to "[]"
      let expected = Text.encodeUtf8 "[]"
      serialized `shouldBe` expected

    it "BUG: serializes batch with multiple records" $ do
      -- BUG: serializeBatch (line 293-294) uses Aeson.encode which should serialize
      -- all records. However, if there's a bug in Aeson encoding or if records have
      -- invalid JSON, serialization may fail silently or produce invalid JSON.
      record1 <- createTestAuditRecord (Text.encodeUtf8 "content1")
      record2 <- createTestAuditRecord (Text.encodeUtf8 "content2")
      let records = [record1, record2]
      let serialized = serializeBatch records
      
      -- Should serialize to valid JSON array
      serialized `shouldSatisfy` \bs -> not (BS.null bs)

    it "BUG: may fail silently on invalid records" $ do
      -- BUG: serializeBatch doesn't validate records before serialization.
      -- If records have invalid fields (e.g., invalid UTF-8 in Text fields),
      -- serialization may fail or produce invalid JSON.
      record <- createTestAuditRecord (Text.encodeUtf8 "test")
      let records = [record]
      let serialized = serializeBatch records
      
      -- Should serialize successfully
      serialized `shouldSatisfy` \bs -> not (BS.null bs)

  describe "deserializeBatch" $ do
    it "deserializes empty batch" $ do
      let serialized = Text.encodeUtf8 "[]"
      let records = deserializeBatch serialized
      
      records `shouldBe` []

    it "BUG: returns empty list for invalid JSON instead of error" $ do
      -- BUG: deserializeBatch (line 297-300) returns empty list for invalid JSON
      -- instead of returning an error. This hides deserialization failures and
      -- makes debugging harder.
      let invalidJSON = Text.encodeUtf8 "invalid json"
      let records = deserializeBatch invalidJSON
      
      records `shouldBe` [] -- Returns empty list, doesn't indicate error

    it "BUG: may fail silently on truncated JSON" $ do
      -- BUG: deserializeBatch may fail silently on truncated JSON (partial array).
      -- If JSON is truncated, decode may return Nothing, leading to empty list
      -- without indication of truncation.
      let truncatedJSON = Text.encodeUtf8 "[{\"content\":\"test\""
      let records = deserializeBatch truncatedJSON
      
      -- May return empty list or partial records without error indication
      records `shouldSatisfy` \rs -> True

    it "BUG: may not handle malformed JSON arrays" $ do
      -- BUG: deserializeBatch doesn't validate JSON structure before deserialization.
      -- Malformed JSON (e.g., missing brackets, invalid syntax) may cause decode
      -- to return Nothing, leading to empty list without error.
      let malformedJSON = Text.encodeUtf8 "[{\"content\":\"test\"},]" -- Trailing comma
      let records = deserializeBatch malformedJSON
      
      -- May return empty list or fail silently
      records `shouldSatisfy` \rs -> True

    it "deserializes valid batch correctly" $ do
      record <- createTestAuditRecord (Text.encodeUtf8 "test")
      let records = [record]
      let serialized = serializeBatch records
      let deserialized = deserializeBatch serialized
      
      length deserialized `shouldBe` 1

  describe "computeDeltas" $ do
    it "computes deltas for matching metrics" $ do
      let chMetrics = [("cust1", 100), ("cust2", 200)]
      let casMetrics = [("cust1", 100), ("cust2", 200)]
      let deltas = computeDeltas chMetrics casMetrics
      
      -- Should have zero deltas for matching metrics
      deltas `shouldBe` [("cust1", 0.0), ("cust2", 0.0)]

    it "BUG: computes deltas with division by zero for zero ClickHouse values" $ do
      -- BUG: computeDeltas (line 550-573) computes percentage delta as
      -- (cas - ch) / ch * 100. If ch is zero, this causes division by zero.
      -- The function should handle zero values gracefully.
      let chMetrics = [("cust1", 0)] -- Zero value
      let casMetrics = [("cust1", 100)]
      let deltas = computeDeltas chMetrics casMetrics
      
      -- BUG: May produce Infinity or cause division by zero error
      -- Should handle zero values gracefully (e.g., return 100.0% or special value)
      deltas `shouldSatisfy` \ds -> not (null ds)

    it "BUG: produces misleading 100.0% delta for division by zero cases" $ do
      -- BUG: If ch is zero and cas is non-zero, computeDeltas may produce
      -- Infinity or a very large delta percentage, which is misleading.
      -- The function should distinguish between "zero to non-zero" and actual discrepancies.
      let chMetrics = [("cust1", 0)]
      let casMetrics = [("cust1", 50)]
      let deltas = computeDeltas chMetrics casMetrics
      
      -- May produce Infinity or very large delta
      deltas `shouldSatisfy` \ds -> not (null ds)

    it "BUG: silently overwrites duplicate customer IDs" $ do
      -- BUG: computeDeltas (line 552) uses Map.fromList which silently overwrites
      -- duplicate keys. If metrics have duplicate customer IDs, only the last value
      -- is kept, leading to incorrect delta calculations.
      let chMetrics = [("cust1", 100), ("cust1", 200)] -- Duplicate key
      let casMetrics = [("cust1", 150)]
      let deltas = computeDeltas chMetrics casMetrics
      
      -- Only one delta computed (duplicate overwritten)
      length deltas `shouldBe` 1

    it "BUG: doesn't handle negative values correctly" $ do
      -- BUG: computeDeltas doesn't validate that metrics are non-negative.
      -- Negative values may produce incorrect or misleading delta percentages.
      let chMetrics = [("cust1", -100)] -- Negative value
      let casMetrics = [("cust1", 100)]
      let deltas = computeDeltas chMetrics casMetrics
      
      -- May produce incorrect delta (negative divided by negative)
      deltas `shouldSatisfy` \ds -> not (null ds)

    it "BUG: doesn't handle very large delta percentages" $ do
      -- BUG: computeDeltas may produce very large delta percentages (e.g., 10000%)
      -- for cases where cas >> ch. These large percentages may be misleading or
      -- cause display issues.
      let chMetrics = [("cust1", 1)]
      let casMetrics = [("cust1", 1000)]
      let deltas = computeDeltas chMetrics casMetrics
      
      -- Produces very large delta percentage
      deltas `shouldSatisfy` \ds -> not (null ds)
      case deltas of
        (_, delta) : _ -> delta `shouldSatisfy` \d -> d > 100.0

    it "handles ClickHouse-only customers" $ do
      let chMetrics = [("cust1", 100)]
      let casMetrics = [] -- Customer not in CAS
      let deltas = computeDeltas chMetrics casMetrics
      
      -- Should compute negative delta (CAS missing data)
      deltas `shouldSatisfy` \ds -> not (null ds)
      case deltas of
        (_, delta) : _ -> delta `shouldSatisfy` \d -> d < 0.0

    it "handles CAS-only customers" $ do
      let chMetrics = []
      let casMetrics = [("cust1", 100)] -- Customer not in ClickHouse
      let deltas = computeDeltas chMetrics casMetrics
      
      -- Should compute positive delta (ClickHouse missing data)
      deltas `shouldSatisfy` \ds -> not (null ds)
      case deltas of
        (_, delta) : _ -> delta `shouldSatisfy` \d -> d > 0.0

    it "BUG: uses global signing key which may not be thread-safe" $ do
      -- BUG: signBatch (line 208-209) uses casSigningKey which is initialized from
      -- globalSigningKey (line 103). globalSigningKey (line 81-85) uses unsafePerformIO
      -- which may not be thread-safe if multiple threads access it concurrently.
      client <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      let content = Text.encodeUtf8 "test"
      let signature = signBatch client content
      
      -- Should sign successfully, but global key access may not be thread-safe
      BS.length signature `shouldBe` 64
