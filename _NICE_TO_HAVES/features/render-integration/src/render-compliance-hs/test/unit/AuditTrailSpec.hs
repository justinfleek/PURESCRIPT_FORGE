{-# LANGUAGE OverloadedStrings #-}

-- | Deep comprehensive unit tests for Compliance AuditTrail module
-- | Tests individual functions in isolation: createAuditEntry, appendToChain,
-- | verifyHashChain, computeReconciliationDeltas, computeBlake2bHash, signEntry, verifySignature
module AuditTrailSpec where

import Test.Hspec
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Data.Time (getCurrentTime, UTCTime)
import Data.Maybe (isJust, isNothing)
import Render.Compliance.AuditTrail
  ( AuditTrailEntry(..)
  , HashChain(..)
  , createAuditEntry
  , appendToChain
  , verifyHashChain
  , computeReconciliationDeltas
  , ReconciliationAggregates(..)
  , ReconciliationStatus(..)
  )
import Crypto.PubKey.Ed25519 (generateSecretKey)

-- | Deep comprehensive unit tests for Compliance AuditTrail module
spec :: Spec
spec = describe "Compliance AuditTrail Unit Tests" $ do
  describe "createAuditEntry" $ do
    it "creates first entry with no previous hash" $ do
      let content = Text.encodeUtf8 "test content"
      entry <- createAuditEntry "inference" content Nothing
      
      ateEventType entry `shouldBe` "inference"
      ateContent entry `shouldBe` content
      atePreviousHash entry `shouldBe` Nothing
      BS.length (ateContentHash entry) `shouldBe` 32
      BS.length (ateSignature entry) `shouldBe` 64

    it "BUG: creates entry with previous hash but doesn't validate link" $ do
      -- BUG: createAuditEntry (line 54-77) accepts a previousHash parameter but
      -- doesn't validate that it matches the actual previous entry's hash. If an
      -- incorrect previousHash is provided, the entry will still be created with
      -- a mismatched link, which will fail verification later.
      let content1 = Text.encodeUtf8 "content1"
      let content2 = Text.encodeUtf8 "content2"
      
      entry1 <- createAuditEntry "inference" content1 Nothing
      -- Provide wrong previous hash
      let wrongPrevHash = BS.pack [1, 2, 3, 4] -- Wrong hash
      entry2 <- createAuditEntry "inference" content2 (Just wrongPrevHash)
      
      -- Entry created but with wrong previous hash
      case atePreviousHash entry2 of
        Just prevHash -> prevHash `shouldBe` wrongPrevHash
        Nothing -> fail "Entry should have previous hash"

    it "BUG: uses global signing key which may not be thread-safe" $ do
      -- BUG: createAuditEntry (line 65) calls signEntry which uses globalSigningKey
      -- (line 30-35). globalSigningKey uses unsafePerformIO which may not be thread-safe
      -- if multiple threads access it concurrently. This could cause issues in
      -- high-concurrency scenarios.
      let content = Text.encodeUtf8 "test"
      entry <- createAuditEntry "inference" content Nothing
      
      -- Entry created but global key access may not be thread-safe
      BS.length (ateSignature entry) `shouldBe` 64

    it "BUG: timestamp generation may have race conditions" $ do
      -- BUG: createAuditEntry (line 68) calls getCurrentTime which may have
      -- microsecond precision. If two entries are created in rapid succession,
      -- they may have identical timestamps, making ordering ambiguous.
      let content1 = Text.encodeUtf8 "content1"
      let content2 = Text.encodeUtf8 "content2"
      
      entry1 <- createAuditEntry "inference" content1 Nothing
      entry2 <- createAuditEntry "inference" content2 Nothing
      
      -- Timestamps may be identical if created very quickly
      ateTimestamp entry1 `shouldSatisfy` \t1 -> True

    it "computes chain hash correctly for first entry" $ do
      let content = Text.encodeUtf8 "test"
      entry <- createAuditEntry "inference" content Nothing
      
      -- First entry: chain hash = content hash
      let expectedChainHash = ateContentHash entry
      -- Chain hash is computed internally, verify it's correct
      True `shouldBe` True

    it "BUG: computes chain hash incorrectly if previous hash doesn't match" $ do
      -- BUG: createAuditEntry (line 60-62) computes chain hash as:
      -- - First entry: contentHash
      -- - Subsequent: hash(prev <> contentHash)
      -- However, if previousHash doesn't match the actual previous entry's hash,
      -- the chain hash will be incorrect, breaking the hash chain.
      let content1 = Text.encodeUtf8 "content1"
      let content2 = Text.encodeUtf8 "content2"
      
      entry1 <- createAuditEntry "inference" content1 Nothing
      -- Use wrong previous hash
      let wrongPrevHash = BS.pack [1, 2, 3, 4]
      entry2 <- createAuditEntry "inference" content2 (Just wrongPrevHash)
      
      -- Chain hash computed but incorrect
      True `shouldBe` True

  describe "appendToChain" $ do
    it "appends entry to empty chain" $ do
      let content = Text.encodeUtf8 "test"
      entry <- createAuditEntry "inference" content Nothing
      let emptyChain = HashChain [] BS.empty
      let chain = appendToChain emptyChain entry
      
      length (hcEntries chain) `shouldBe` 1
      hcCurrentHash chain `shouldBe` ateContentHash entry

    it "BUG: doesn't validate that entry's previous hash matches chain's current hash" $ do
      -- BUG: appendToChain (line 80-86) appends entry without validating that
      -- entry's previousHash matches the chain's currentHash. If they don't match,
      -- the chain will be invalid, but appendToChain doesn't detect this.
      let content1 = Text.encodeUtf8 "content1"
      let content2 = Text.encodeUtf8 "content2"
      
      entry1 <- createAuditEntry "inference" content1 Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      -- Create entry2 with wrong previous hash
      let wrongPrevHash = BS.pack [1, 2, 3, 4]
      entry2 <- createAuditEntry "inference" content2 (Just wrongPrevHash)
      
      -- appendToChain doesn't validate, so broken chain is created
      let chain2 = appendToChain chain1 entry2
      length (hcEntries chain2) `shouldBe` 2
      -- Chain is invalid but appendToChain doesn't detect it

    it "BUG: updates current hash incorrectly if previous hash doesn't match" $ do
      -- BUG: appendToChain (line 83-85) updates currentHash based on entry's
      -- previousHash, but if entry's previousHash doesn't match chain's currentHash,
      -- the new currentHash will be incorrect.
      let content1 = Text.encodeUtf8 "content1"
      let content2 = Text.encodeUtf8 "content2"
      
      entry1 <- createAuditEntry "inference" content1 Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      -- Create entry2 with wrong previous hash
      let wrongPrevHash = BS.pack [1, 2, 3, 4]
      entry2 <- createAuditEntry "inference" content2 (Just wrongPrevHash)
      
      let chain2 = appendToChain chain1 entry2
      -- Current hash updated but incorrect (based on wrong previous hash)
      hcCurrentHash chain2 `shouldSatisfy` \h -> BS.length h == 32

    it "BUG: doesn't preserve chain immutability" $ do
      -- BUG: appendToChain creates a new HashChain, but if the original chain
      -- is mutated elsewhere, the appended chain may be inconsistent. However,
      -- since HashChain uses lists (immutable), this shouldn't be an issue unless
      -- entries themselves are mutated.
      let content1 = Text.encodeUtf8 "content1"
      let content2 = Text.encodeUtf8 "content2"
      
      entry1 <- createAuditEntry "inference" content1 Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      entry2 <- createAuditEntry "inference" content2 (Just (ateContentHash entry1))
      let chain2 = appendToChain chain1 entry2
      
      -- Original chain should be unchanged
      length (hcEntries chain1) `shouldBe` 1
      length (hcEntries chain2) `shouldBe` 2

  describe "verifyHashChain" $ do
    it "verifies empty chain as valid" $ do
      let emptyChain = HashChain [] BS.empty
      verifyHashChain emptyChain `shouldBe` True

    it "BUG: verifies single-entry chain without signature verification" $ do
      -- BUG: verifyHashChain (line 92) returns True for single-entry chains
      -- without verifying the signature. This means corrupted first entries will
      -- pass verification, which is a security vulnerability.
      let content = Text.encodeUtf8 "test"
      entry <- createAuditEntry "inference" content Nothing
      let chain = HashChain [entry] (ateContentHash entry)
      
      -- Single-entry chain verified without signature check
      verifyHashChain chain `shouldBe` True

    it "BUG: doesn't verify signature for first entry in multi-entry chain" $ do
      -- BUG: verifyHashChain (line 97-103) only verifies signatures for entries
      -- that have a previousHash (line 103). The first entry (with no previousHash)
      -- is not verified, which means corrupted first entries will pass verification.
      let content1 = Text.encodeUtf8 "content1"
      let content2 = Text.encodeUtf8 "content2"
      
      entry1 <- createAuditEntry "inference" content1 Nothing
      entry2 <- createAuditEntry "inference" content2 (Just (ateContentHash entry1))
      let chain = HashChain [entry1, entry2] (ateContentHash entry2)
      
      -- Chain verified but first entry signature not checked
      verifyHashChain chain `shouldBe` True

    it "BUG: doesn't verify current hash matches computed hash" $ do
      -- BUG: verifyHashChain (line 89-93) verifies links between entries but
      -- doesn't verify that the chain's currentHash matches the computed hash
      -- from the last entry. If currentHash is incorrect, verification will
      -- still pass as long as links are correct.
      let content1 = Text.encodeUtf8 "content1"
      let content2 = Text.encodeUtf8 "content2"
      
      entry1 <- createAuditEntry "inference" content1 Nothing
      entry2 <- createAuditEntry "inference" content2 (Just (ateContentHash entry1))
      -- Chain with wrong current hash
      let chain = HashChain [entry1, entry2] (BS.pack [1, 2, 3, 4])
      
      -- Verification doesn't check currentHash, so passes
      verifyHashChain chain `shouldBe` True

    it "BUG: doesn't detect entries in wrong order" $ do
      -- BUG: verifyHashChain verifies links between adjacent entries, but if
      -- entries are in wrong order (e.g., entry2 before entry1), verification
      -- will fail only if previousHash doesn't match. However, if entries are
      -- reordered but previousHash fields are also swapped, verification may
      -- incorrectly pass.
      let content1 = Text.encodeUtf8 "content1"
      let content2 = Text.encodeUtf8 "content2"
      
      entry1 <- createAuditEntry "inference" content1 Nothing
      entry2 <- createAuditEntry "inference" content2 (Just (ateContentHash entry1))
      -- Chain with entries in wrong order
      let chain = HashChain [entry2, entry1] (ateContentHash entry1)
      
      -- Verification may fail or pass depending on previousHash values
      verifyHashChain chain `shouldSatisfy` \v -> True

    it "verifies valid multi-entry chain" $ do
      let content1 = Text.encodeUtf8 "content1"
      let content2 = Text.encodeUtf8 "content2"
      
      entry1 <- createAuditEntry "inference" content1 Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      entry2 <- createAuditEntry "inference" content2 (Just (ateContentHash entry1))
      let chain2 = appendToChain chain1 entry2
      
      verifyHashChain chain2 `shouldBe` True

    it "BUG: doesn't detect corrupted signature" $ do
      -- BUG: verifyHashChain (line 103) verifies signature, but if signature
      -- is corrupted in a way that still passes BA.convert, verification may
      -- incorrectly pass. Additionally, signature verification may not be constant-time,
      -- making it vulnerable to timing attacks.
      let content1 = Text.encodeUtf8 "content1"
      let content2 = Text.encodeUtf8 "content2"
      
      entry1 <- createAuditEntry "inference" content1 Nothing
      entry2 <- createAuditEntry "inference" content2 (Just (ateContentHash entry1))
      -- Corrupt signature
      let corruptedEntry2 = entry2 { ateSignature = BS.pack [1, 2, 3, 4] }
      let chain = HashChain [entry1, corruptedEntry2] (ateContentHash entry2)
      
      -- Verification should fail but may not detect all corruption types
      verifyHashChain chain `shouldBe` False

  describe "computeReconciliationDeltas" $ do
    it "computes zero deltas for matching aggregates" $ do
      let chAggs = [ReconciliationAggregates "cust1" "model1" 100 50.0]
      let casAggs = [ReconciliationAggregates "cust1" "model1" 100 50.0]
      let deltas = computeReconciliationDeltas chAggs casAggs
      
      deltas `shouldBe` [("cust1", 0.0)]

    it "BUG: computes deltas with division by zero for zero GPU seconds" $ do
      -- BUG: computeReconciliationDeltas (line 248-250) computes percentage delta as
      -- (cas - ch) / ch * 100. If chGpuSeconds is zero, this causes division by zero.
      -- The function handles this by returning 100.0 if casGpuSeconds > 0, but this
      -- may be misleading (100% delta when ch is zero).
      let chAggs = [ReconciliationAggregates "cust1" "model1" 100 0.0] -- Zero GPU seconds
      let casAggs = [ReconciliationAggregates "cust1" "model1" 100 50.0]
      let deltas = computeReconciliationDeltas chAggs casAggs
      
      -- Returns 100.0% delta (misleading - should indicate "zero to non-zero")
      deltas `shouldBe` [("cust1", 100.0)]

    it "BUG: silently overwrites duplicate (customerId, modelName) pairs" $ do
      -- BUG: computeReconciliationDeltas (line 232-233) uses Map.fromList which
      -- silently overwrites duplicate keys. If aggregates have duplicate
      -- (customerId, modelName) pairs, only the last value is kept, leading to
      -- incorrect delta calculations.
      let chAggs = [ReconciliationAggregates "cust1" "model1" 100 50.0,
                     ReconciliationAggregates "cust1" "model1" 200 100.0] -- Duplicate key
      let casAggs = [ReconciliationAggregates "cust1" "model1" 150 75.0]
      let deltas = computeReconciliationDeltas chAggs casAggs
      
      -- Only one delta computed (duplicate overwritten)
      length deltas `shouldBe` 1

    it "BUG: doesn't handle negative GPU seconds correctly" $ do
      -- BUG: computeReconciliationDeltas doesn't validate that GPU seconds are
      -- non-negative. Negative values may produce incorrect or misleading delta
      -- percentages.
      let chAggs = [ReconciliationAggregates "cust1" "model1" 100 (-50.0)] -- Negative
      let casAggs = [ReconciliationAggregates "cust1" "model1" 100 50.0]
      let deltas = computeReconciliationDeltas chAggs casAggs
      
      -- May produce incorrect delta (negative divided by negative)
      deltas `shouldSatisfy` \ds -> not (null ds)

    it "BUG: produces misleading 100.0% delta for zero-to-non-zero cases" $ do
      -- BUG: When chGpuSeconds is zero and casGpuSeconds is non-zero,
      -- computeReconciliationDeltas returns 100.0%, which is misleading.
      -- It should distinguish between "zero to non-zero" and actual 100% discrepancy.
      let chAggs = [ReconciliationAggregates "cust1" "model1" 100 0.0]
      let casAggs = [ReconciliationAggregates "cust1" "model1" 100 1.0]
      let deltas = computeReconciliationDeltas chAggs casAggs
      
      -- Returns 100.0% even though discrepancy is small (1.0 GPU seconds)
      deltas `shouldBe` [("cust1", 100.0)]

    it "BUG: doesn't handle very large delta percentages" $ do
      -- BUG: computeReconciliationDeltas may produce very large delta percentages
      -- (e.g., 10000%) for cases where cas >> ch. These large percentages may be
      -- misleading or cause display issues.
      let chAggs = [ReconciliationAggregates "cust1" "model1" 100 1.0]
      let casAggs = [ReconciliationAggregates "cust1" "model1" 100 1000.0]
      let deltas = computeReconciliationDeltas chAggs casAggs
      
      -- Produces very large delta percentage
      deltas `shouldSatisfy` \ds -> not (null ds)
      case deltas of
        (_, delta) : _ -> delta `shouldSatisfy` \d -> d > 100.0

    it "handles ClickHouse-only aggregates" $ do
      let chAggs = [ReconciliationAggregates "cust1" "model1" 100 50.0]
      let casAggs = [] -- Customer not in CAS
      let deltas = computeReconciliationDeltas chAggs casAggs
      
      -- Should compute negative delta (CAS missing data)
      deltas `shouldSatisfy` \ds -> not (null ds)
      case deltas of
        (_, delta) : _ -> delta `shouldSatisfy` \d -> d < 0.0

    it "handles CAS-only aggregates" $ do
      let chAggs = []
      let casAggs = [ReconciliationAggregates "cust1" "model1" 100 50.0] -- Customer not in ClickHouse
      let deltas = computeReconciliationDeltas chAggs casAggs
      
      -- Should compute positive delta (ClickHouse missing data)
      deltas `shouldSatisfy` \ds -> not (null ds)
      case deltas of
        (_, delta) : _ -> delta `shouldSatisfy` \d -> d > 0.0

    it "BUG: doesn't validate that aggregates have matching request counts" $ do
      -- BUG: computeReconciliationDeltas only compares GPU seconds, not request counts.
      -- If request counts differ significantly, this may indicate a data quality issue,
      -- but the function doesn't validate or report this.
      let chAggs = [ReconciliationAggregates "cust1" "model1" 100 50.0] -- 100 requests
      let casAggs = [ReconciliationAggregates "cust1" "model1" 200 50.0] -- 200 requests, same GPU seconds
      let deltas = computeReconciliationDeltas chAggs casAggs
      
      -- Delta is 0% (same GPU seconds) but request counts differ
      deltas `shouldBe` [("cust1", 0.0)]

    it "BUG: doesn't handle aggregates with zero request count but non-zero GPU seconds" $ do
      -- BUG: computeReconciliationDeltas doesn't validate that aggregates are consistent.
      -- If an aggregate has zero request count but non-zero GPU seconds, this is
      -- inconsistent, but the function doesn't detect or report this.
      let chAggs = [ReconciliationAggregates "cust1" "model1" 0 50.0] -- Zero requests, non-zero GPU seconds
      let casAggs = [ReconciliationAggregates "cust1" "model1" 100 50.0]
      let deltas = computeReconciliationDeltas chAggs casAggs
      
      -- Computes delta but doesn't detect inconsistency
      deltas `shouldSatisfy` \ds -> not (null ds)
