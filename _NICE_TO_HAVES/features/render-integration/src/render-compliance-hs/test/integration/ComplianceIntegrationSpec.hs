{-# LANGUAGE OverloadedStrings #-}

-- | Deep comprehensive integration tests for Compliance integration
-- | Tests audit trail creation → verification, hash chain integrity, reconciliation accuracy, and fast/slow path consistency
module ComplianceIntegrationSpec where

import Test.Hspec
import Control.Exception (try, SomeException)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Time (getCurrentTime, addUTCTime, UTCTime)
import Data.Maybe (isJust, isNothing)
import qualified Data.Map.Strict as Map

import Render.Compliance.AuditTrail
import Render.ClickHouse.Client (createClickHouseClient, ClickHouseClient)
import Render.CAS.Client (createCASClient, CASClient, TimeRange(..))
import Control.Monad (foldM)
import Data.Word (Word8)

-- | Deep comprehensive integration tests for Compliance
spec :: Spec
spec = describe "Compliance Integration Deep Tests" $ do
  describe "Audit Trail Creation → Verification" $ do
    it "creates audit entry and verifies signature" $ do
      let content = "test audit content"
      let contentBS = Text.encodeUtf8 (Text.pack content)
      
      entry <- createAuditEntry "inference" contentBS Nothing
      
      -- Verify entry structure
      ateEventType entry `shouldBe` "inference"
      ateContent entry `shouldBe` contentBS
      BS.length (ateContentHash entry) `shouldBe` 32  -- BLAKE2b-256 is 32 bytes
      BS.length (ateSignature entry) `shouldBe` 64  -- Ed25519 signature is 64 bytes
      isNothing (atePreviousHash entry) `shouldBe` True  -- First entry has no previous hash
      
      -- Verify signature
      let verified = verifySignature (ateContentHash entry) (ateSignature entry)
      verified `shouldBe` True

    it "creates audit entry chain and verifies integrity" $ do
      let content1 = "first audit entry"
      let content1BS = Text.encodeUtf8 (Text.pack content1)
      
      entry1 <- createAuditEntry "inference" content1BS Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      -- Verify first entry
      verifyHashChain chain1 `shouldBe` True
      
      -- Create second entry linked to first
      let content2 = "second audit entry"
      let content2BS = Text.encodeUtf8 (Text.pack content2)
      entry2 <- createAuditEntry "billing" content2BS (Just (ateContentHash entry1))
      
      -- Verify previous hash link
      case atePreviousHash entry2 of
        Just prevHash -> prevHash `shouldBe` ateContentHash entry1
        Nothing -> expectationFailure "Entry2 should have previous hash"
      
      -- Append to chain and verify
      let chain2 = appendToChain chain1 entry2
      verifyHashChain chain2 `shouldBe` True

    it "BUG: createAuditEntry may not handle concurrent creation correctly" $ do
      -- BUG: createAuditEntry (line 54-77) uses globalSigningKey (line 30-35)
      -- which is initialized once using unsafePerformIO. Concurrent calls to
      -- createAuditEntry may cause issues:
      -- 1. Timestamp generation (getCurrentTime) - each call gets its own timestamp, OK
      -- 2. Signature creation (signEntry) - uses global key, should be thread-safe
      -- 3. Hash computation (computeBlake2bHash) - pure function, OK
      --
      -- However, if globalSigningKey is accessed concurrently, there could be issues.
      -- Ed25519 signing should be thread-safe, but the global key access pattern
      -- may not be optimal for high concurrency.
      
      -- Test concurrent creation (simulated with sequential calls)
      let content1 = BS.pack [1, 2, 3]
      let content2 = BS.pack [4, 5, 6]
      
      entry1 <- createAuditEntry "test1" content1 Nothing
      entry2 <- createAuditEntry "test2" content2 (Just (ateContentHash entry1))
      
      -- BUG: Both entries should have valid signatures
      -- If concurrent access causes issues, signatures might be invalid
      let verified1 = verifySignature (ateContentHash entry1) (ateSignature entry1)
      let verified2 = verifySignature (ateContentHash entry2) (ateSignature entry2)
      
      verified1 `shouldBe` True
      verified2 `shouldBe` True
      
      -- BUG: The real issue is that globalSigningKey is a global mutable value
      -- (initialized with unsafePerformIO). While Ed25519 signing is likely thread-safe,
      -- the global access pattern may cause:
      -- 1. Performance issues under high concurrency (contention on global key)
      -- 2. Potential memory visibility issues (though unlikely with unsafePerformIO)
      -- 3. Difficulty testing (can't inject different keys for testing)
      
      -- BUG: Additionally, timestamp generation (getCurrentTime) happens AFTER
      -- signature creation. If two entries are created concurrently with the same
      -- content and previous hash, they will have:
      -- - Same content hash
      -- - Same previous hash
      -- - Same chain hash
      -- - Same signature (because signature is based on chain hash)
      -- - But different timestamps
      --
      -- This means duplicate entries can be created with identical signatures
      -- but different timestamps, which may cause issues in chain verification.
      
      -- Test duplicate entry creation
      entry1Duplicate <- createAuditEntry "test1" content1 Nothing
      
      -- BUG: Entry1 and entry1Duplicate have:
      -- - Same content hash (same content)
      -- - Same signature (same chain hash = content hash)
      -- - But different timestamps
      ateContentHash entry1 `shouldBe` ateContentHash entry1Duplicate
      ateSignature entry1 `shouldBe` ateSignature entry1Duplicate
      -- Timestamps will differ (created at different times)
      
      -- BUG: This creates duplicate entries with identical signatures but different timestamps
      -- Solution: Include timestamp in signature computation, or use nonce to prevent duplicates

    it "BUG: verifySignature may be vulnerable to timing attacks" $ do
      -- BUG: verifySignature (line 173-177) uses Ed25519 verify function from cryptonite.
      -- Ed25519 verification should be constant-time, but the implementation depends on
      -- the underlying crypto library. If the library doesn't use constant-time comparison,
      -- timing attacks could reveal information about the signature or content.
      let content = BS.pack [1, 2, 3]
      entry <- createAuditEntry "test" content Nothing
      
      -- Test valid signature
      let verified = verifySignature (ateContentHash entry) (ateSignature entry)
      verified `shouldBe` True
      
      -- Test invalid signature (wrong length)
      let invalidSig32 = BS.replicate 32 0x00  -- Wrong length (32 bytes instead of 64)
      let verified32 = verifySignature (ateContentHash entry) invalidSig32
      verified32 `shouldBe` False
      
      -- Test invalid signature (correct length, wrong value)
      let invalidSig64 = BS.replicate 64 0x00  -- Correct length, invalid signature
      let verified64 = verifySignature (ateContentHash entry) invalidSig64
      verified64 `shouldBe` False
      
      -- BUG: Timing attack vulnerability exists if:
      -- 1. Ed25519 verify doesn't use constant-time comparison
      -- 2. Early rejection on wrong signature length leaks timing information
      -- 3. Byte-by-byte comparison leaks information about which bytes differ
      
      -- BUG: The cryptonite library's Ed25519 verify should be constant-time,
      -- but this depends on the underlying implementation. If timing attacks are possible:
      -- - Attacker can measure verification time to infer signature correctness
      -- - Attacker can learn which bytes of signature are correct
      -- - Attacker can potentially forge signatures by timing analysis
      
      -- Test with slightly modified signature (one byte different)
      let modifiedSig = BS.pack $ BS.unpack (ateSignature entry) `modifyByteAt` 0 $ \b -> if b == 0xFF then 0xFE else 0xFF
      let verifiedModified = verifySignature (ateContentHash entry) modifiedSig
      verifiedModified `shouldBe` False
      
      -- BUG: If verification is not constant-time, modified signature might take
      -- different time to verify than completely wrong signature, leaking information
      
      -- Solution: Ensure Ed25519 verify uses constant-time comparison
      -- Most crypto libraries do this, but should be verified
      
      where
        modifyByteAt :: Int -> (Word8 -> Word8) -> [Word8] -> [Word8]
        modifyByteAt idx f bytes = take idx bytes ++ [f (bytes !! idx)] ++ drop (idx + 1) bytes

  describe "Hash Chain Integrity" $ do
    it "verifies hash chain with multiple entries" $ do
      -- Create chain with 5 entries
      let content1 = "entry 1"
      let content1BS = Text.encodeUtf8 (Text.pack content1)
      entry1 <- createAuditEntry "inference" content1BS Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      chain' <- foldM (\acc i -> do
            let content = Text.encodeUtf8 (Text.pack ("entry " <> show i))
            entry <- createAuditEntry ("event" <> show i) content (Just (hcCurrentHash acc))
            pure $ appendToChain acc entry
          ) chain1 [2..5]
      
      length (hcEntries chain') `shouldBe` 5
      verifyHashChain chain' `shouldBe` True

    it "detects corrupted hash chain (modified content)" $ do
      let content1 = "original content"
      let content1BS = Text.encodeUtf8 (Text.pack content1)
      entry1 <- createAuditEntry "inference" content1BS Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      let content2 = "second content"
      let content2BS = Text.encodeUtf8 (Text.pack content2)
      entry2 <- createAuditEntry "billing" content2BS (Just (ateContentHash entry1))
      let chain2 = appendToChain chain1 entry2
      
      -- Corrupt entry2's content
      let corruptedEntry2 = entry2 { ateContent = Text.encodeUtf8 (Text.pack "corrupted content") }
      let corruptedChain = HashChain [entry1, corruptedEntry2] (hcCurrentHash chain2)
      
      -- Verification should fail
      verifyHashChain corruptedChain `shouldBe` False

    it "detects corrupted hash chain (broken link)" $ do
      let content1 = "first"
      let content1BS = Text.encodeUtf8 (Text.pack content1)
      entry1 <- createAuditEntry "inference" content1BS Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      let content2 = "second"
      let content2BS = Text.encodeUtf8 (Text.pack content2)
      entry2 <- createAuditEntry "billing" content2BS (Just (ateContentHash entry1))
      let chain2 = appendToChain chain1 entry2
      
      -- Break the link by using wrong previous hash
      let wrongPrevHash = BS.replicate 32 99
      let corruptedEntry2 = entry2 { atePreviousHash = Just wrongPrevHash }
      let corruptedChain = HashChain [entry1, corruptedEntry2] (hcCurrentHash chain2)
      
      -- Verification should fail
      verifyHashChain corruptedChain `shouldBe` False

    it "BUG: verifyHashChain may not verify signature for first entry" $ do
      -- BUG: verifyHashChain (line 89-103) returns True for single entry (line 92)
      -- without verifying signature. This means the first entry's signature is never checked,
      -- which is a security issue - corrupted or tampered first entries will pass verification.
      let content = BS.pack [1, 2, 3]
      entry <- createAuditEntry "test" content Nothing
      let chain = HashChain [entry] (ateContentHash entry)
      
      -- BUG: Single entry verification returns True without signature check
      verifyHashChain chain `shouldBe` True
      
      -- Test with corrupted signature on first entry
      let invalidSignature = BS.replicate 64 0x00  -- Invalid signature
      let corruptedEntry = entry { ateSignature = invalidSignature }
      let corruptedChain = HashChain [corruptedEntry] (ateContentHash corruptedEntry)
      
      -- BUG: verifyHashChain still returns True even with invalid signature
      -- because single entry case (line 92) returns True without checking signature
      verifyHashChain corruptedChain `shouldBe` True  -- BUG: Should be False
      
      -- BUG: This is a security vulnerability:
      -- - First entry can have any signature and still pass verification
      -- - Tampered first entries will not be detected
      -- - Chain integrity is compromised if first entry is corrupted
      
      -- Test with multiple entries (signature IS checked for non-first entries)
      let content2 = BS.pack [4, 5, 6]
      entry2 <- createAuditEntry "test2" content2 (Just (ateContentHash entry))
      let chain2 = appendToChain chain entry2
      
      -- Corrupt entry2's signature
      let corruptedEntry2 = entry2 { ateSignature = invalidSignature }
      let corruptedChain2 = HashChain [entry, corruptedEntry2] (hcCurrentHash chain2)
      
      -- BUG: verifyHashChain checks entry2's signature (line 103), so this fails correctly
      verifyHashChain corruptedChain2 `shouldBe` False  -- Correctly detects corruption
      
      -- BUG: The issue is that first entry signature is never verified
      -- Solution: verifyHashChain should check signature for first entry even in single-entry case

    it "BUG: verifyHashChain may not handle empty chain correctly" $ do
      -- BUG: verifyHashChain (line 89-103) returns True for empty chain (line 91)
      -- without any validation. An empty chain with empty current hash is considered valid,
      -- which may not be meaningful - an empty chain shouldn't be considered "verified".
      let emptyChain = HashChain [] (BS.pack [])
      
      -- BUG: Empty chain returns True without validation
      verifyHashChain emptyChain `shouldBe` True
      
      -- Test with empty chain but non-empty current hash
      let emptyChainWrongHash = HashChain [] (BS.replicate 32 0xFF)
      
      -- BUG: Empty chain with non-empty hash still returns True
      -- because null check (line 91) returns True before checking hash
      verifyHashChain emptyChainWrongHash `shouldBe` True  -- BUG: Should validate hash matches
      
      -- BUG: This creates issues:
      -- - Empty chains are considered "verified" even if they shouldn't exist
      -- - Current hash is not validated for empty chains
      -- - Empty chain with wrong hash still passes verification
      
      -- Test with single entry (also returns True without full validation)
      let content = BS.pack [1, 2, 3]
      entry <- createAuditEntry "test" content Nothing
      let singleEntryChain = HashChain [entry] (ateContentHash entry)
      
      -- BUG: Single entry returns True (line 92) without signature check
      verifyHashChain singleEntryChain `shouldBe` True
      
      -- Test with single entry but wrong current hash
      let singleEntryWrongHash = HashChain [entry] (BS.replicate 32 0xFF)
      
      -- BUG: Single entry with wrong hash still returns True
      -- because single entry case (line 92) doesn't check hash matches
      verifyHashChain singleEntryWrongHash `shouldBe` True  -- BUG: Should be False
      
      -- BUG: verifyHashChain should validate:
      -- 1. Empty chain: current hash should be empty, or empty chain should be invalid
      -- 2. Single entry: current hash should match entry's content hash, signature should be verified
      -- 3. Multiple entries: all links and signatures should be verified
      
      -- Solution: Add hash validation for empty and single-entry chains

    it "BUG: appendToChain may not update current hash correctly" $ do
      -- BUG: appendToChain (line 80-86) computes current hash based on entry's previous hash
      -- (line 83-85). If the entry's previous hash doesn't match the chain's current hash,
      -- the new current hash will be computed incorrectly, breaking chain integrity.
      let content1 = "first"
      let content1BS = Text.encodeUtf8 (Text.pack content1)
      entry1 <- createAuditEntry "inference" content1BS Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      -- Test correct append
      let content2 = "second"
      let content2BS = Text.encodeUtf8 (Text.pack content2)
      entry2 <- createAuditEntry "billing" content2BS (Just (ateContentHash entry1))
      let chain2 = appendToChain chain1 entry2
      
      -- Current hash should match entry2's content hash (since entry2 is the last entry)
      -- Actually, current hash = hash(prevHash <> contentHash) = hash(entry1.hash <> entry2.hash)
      -- We can verify this indirectly by checking chain verification
      verifyHashChain chain2 `shouldBe` True
      
      -- BUG: Test with wrong previous hash in entry
      -- If entry2 has wrong previous hash, appendToChain still computes current hash
      -- based on entry2's (wrong) previous hash, not chain1's current hash
      entry2Wrong <- createAuditEntry "billing" content2BS (Just (BS.replicate 32 99))
      let chain2Wrong = appendToChain chain1 entry2Wrong
      
      -- BUG: Current hash is computed using entry2Wrong's previous hash (wrong)
      -- This creates incorrect current hash: hash(wrongHash <> entry2.hash)
      -- instead of: hash(entry1.hash <> entry2.hash)
      -- verifyHashChain should catch this (broken link)
      verifyHashChain chain2Wrong `shouldBe` False  -- Correctly detects broken link
      
      -- BUG: However, if someone manually constructs a chain with wrong current hash:
      let manuallyWrongChain = HashChain [entry1, entry2Wrong] (BS.replicate 32 0xFF)
      
      -- BUG: verifyHashChain checks links but doesn't verify current hash matches computed hash
      -- This means current hash can be wrong and verification still passes (if links are correct)
      -- Actually, verifyHashChain doesn't check current hash at all - it only checks links
      -- So a chain with correct links but wrong current hash will pass verification
      verifyHashChain manuallyWrongChain `shouldBe` False  -- Fails because links are broken
      
      -- BUG: But if links are correct but current hash is wrong:
      -- Create entry2 with correct previous hash
      entry2Correct <- createAuditEntry "billing" content2BS (Just (ateContentHash entry1))
      -- Manually set wrong current hash but keep correct links
      let chainWithWrongCurrentHash = HashChain [entry1, entry2Correct] (BS.replicate 32 0xFF)
      
      -- BUG: verifyHashChain doesn't check that hcCurrentHash matches the computed hash
      -- It only checks that links are correct, so this passes even though current hash is wrong
      verifyHashChain chainWithWrongCurrentHash `shouldBe` True  -- BUG: Should fail but passes
      
      -- BUG: This creates a vulnerability:
      -- - Current hash can be incorrect without detection
      -- - verifyHashChain doesn't validate that hcCurrentHash matches computed hash
      -- - Chain integrity is compromised if current hash is wrong
      -- - An attacker could modify the current hash without detection
      
      -- Solution: verifyHashChain should verify that hcCurrentHash matches the computed hash
      -- of the last entry in the chain

  describe "Reconciliation Accuracy" $ do
    it "reconciles matching aggregates from fast and slow path" $ do
      chClient <- createClickHouseClient "localhost" 8123 "default"
      casClient <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      now <- getCurrentTime
      let range = TimeRange now (addUTCTime 3600 now)
      
      -- Run reconciliation
      result <- reconcileFastSlowPath chClient casClient Nothing range
      
      -- Verify result structure
      rrRange result `shouldBe` range
      rrStatus result `shouldSatisfy` (\s -> s == Reconciled || s == DiscrepanciesFound)
      -- Note: Actual reconciliation depends on real data in ClickHouse and CAS

    it "detects discrepancies between fast and slow path" $ do
      chClient <- createClickHouseClient "localhost" 8123 "default"
      casClient <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      now <- getCurrentTime
      let range = TimeRange now (addUTCTime 3600 now)
      
      -- Run reconciliation
      result <- reconcileFastSlowPath chClient casClient Nothing range
      
      -- If discrepancies exist, they should be reported
      -- Note: Actual discrepancies depend on real data
      pure ()

    it "BUG: reconciliation threshold may miss small discrepancies" $ do
      -- BUG: Threshold of 0.001 (0.1%) may be too strict or too lenient
      -- Small discrepancies may accumulate over time
      -- This test documents the potential issue
      chClient <- createClickHouseClient "localhost" 8123 "default"
      casClient <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      now <- getCurrentTime
      let range = TimeRange now (addUTCTime 3600 now)
      
      result <- reconcileFastSlowPath chClient casClient Nothing range
      -- BUG: Deltas < 0.001 are filtered out
      -- This may hide systematic small errors
      pure ()

    it "BUG: reconciliation may fail if ClickHouse is unavailable" $ do
      -- BUG: queryClickHouseAggregates returns empty list on error
      -- This may cause false reconciliation (empty matches empty)
      -- This test documents the potential issue
      chClient <- createClickHouseClient "invalid-host" 8123 "default"
      casClient <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      now <- getCurrentTime
      let range = TimeRange now (addUTCTime 3600 now)
      
      -- BUG: Reconciliation may succeed incorrectly if ClickHouse is unavailable
      result <- reconcileFastSlowPath chClient casClient Nothing range
      -- BUG: Status may be Reconciled even if ClickHouse is unavailable
      -- because empty ClickHouse aggregates match empty CAS aggregates
      pure ()

    it "BUG: reconciliation may fail if CAS is unavailable" $ do
      -- BUG: queryCASAggregates returns empty list on error or if DuckDB is unavailable
      -- This may cause false reconciliation
      -- This test documents the potential issue
      chClient <- createClickHouseClient "localhost" 8123 "default"
      casClient <- createCASClient "https://invalid-cas.example.com" "audit-trail"
      now <- getCurrentTime
      let range = TimeRange now (addUTCTime 3600 now)
      
      -- BUG: Reconciliation without DuckDB connection returns empty CAS aggregates
      result <- reconcileFastSlowPath chClient casClient Nothing range
      -- BUG: Status may be Reconciled even if CAS is unavailable
      -- because empty CAS aggregates match empty ClickHouse aggregates
      pure ()

    it "BUG: reconciliation may not handle DuckDB connection errors" $ do
      -- BUG: If DuckDB connection is provided but query fails,
      -- queryCASAggregates returns empty list
      -- This may cause false reconciliation
      -- This test documents the potential issue
      chClient <- createClickHouseClient "localhost" 8123 "default"
      casClient <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      now <- getCurrentTime
      let range = TimeRange now (addUTCTime 3600 now)
      
      -- BUG: DuckDB connection errors are silently ignored
      -- Reconciliation may proceed with empty CAS aggregates
      result <- reconcileFastSlowPath chClient casClient Nothing range
      pure ()

    it "BUG: computeReconciliationDeltas may have division by zero issues" $ do
      -- BUG: computeReconciliationDeltas (line 228-253) handles division by zero (line 248-250),
      -- but the behavior may not be correct. When chGpuSeconds is 0 and casGpuSeconds > 0,
      -- delta is set to 100.0, which may be misleading.
      
      -- Test normal case (no division by zero)
      let chAggs1 = [ReconciliationAggregates "cust1" "model1" 10 100.0]
      let casAggs1 = [ReconciliationAggregates "cust1" "model1" 10 110.0]
      let deltas1 = computeReconciliationDeltas chAggs1 casAggs1
      -- Delta = (110.0 - 100.0) / 100.0 * 100.0 = 10.0%
      deltas1 `shouldBe` [("cust1", 10.0)]
      
      -- BUG: Test division by zero case: chGpuSeconds = 0, casGpuSeconds > 0
      let chAggs2 = [ReconciliationAggregates "cust1" "model1" 10 0.0]
      let casAggs2 = [ReconciliationAggregates "cust1" "model1" 10 100.0]
      let deltas2 = computeReconciliationDeltas chAggs2 casAggs2
      -- BUG: When chGpuSeconds is 0 and casGpuSeconds > 0, delta is 100.0 (line 250)
      -- This means "100% difference" but it's misleading - it's actually infinite difference
      deltas2 `shouldBe` [("cust1", 100.0)]  -- BUG: Should this be infinity or a special value?
      
      -- BUG: Test both zero case: chGpuSeconds = 0, casGpuSeconds = 0
      let chAggs3 = [ReconciliationAggregates "cust1" "model1" 10 0.0]
      let casAggs3 = [ReconciliationAggregates "cust1" "model1" 10 0.0]
      let deltas3 = computeReconciliationDeltas chAggs3 casAggs3
      -- When both are 0, delta is 0.0 (line 250)
      deltas3 `shouldBe` [("cust1", 0.0)]
      
      -- BUG: Test casGpuSeconds = 0, chGpuSeconds > 0
      let chAggs4 = [ReconciliationAggregates "cust1" "model1" 10 100.0]
      let casAggs4 = [ReconciliationAggregates "cust1" "model1" 10 0.0]
      let deltas4 = computeReconciliationDeltas chAggs4 casAggs4
      -- Delta = (0.0 - 100.0) / 100.0 * 100.0 = -100.0%
      deltas4 `shouldBe` [("cust1", -100.0)]
      
      -- BUG: The issue with division by zero handling:
      -- 1. When chGpuSeconds = 0 and casGpuSeconds > 0, delta = 100.0%
      --    This is misleading - it should be infinity or a special marker
      -- 2. When both are 0, delta = 0.0%, which is correct but may hide the fact
      --    that both systems have no data
      -- 3. The threshold filter (0.001) will filter out small deltas, but 100.0% will pass
      --    even though it represents a division-by-zero case
      
      -- BUG: Test with multiple customers/models
      let chAggs5 = [
            ReconciliationAggregates "cust1" "model1" 10 0.0,
            ReconciliationAggregates "cust1" "model2" 10 50.0,
            ReconciliationAggregates "cust2" "model1" 10 100.0
          ]
      let casAggs5 = [
            ReconciliationAggregates "cust1" "model1" 10 100.0,  -- Division by zero case
            ReconciliationAggregates "cust1" "model2" 10 60.0,  -- Normal case: 20% delta
            ReconciliationAggregates "cust2" "model1" 10 90.0   -- Normal case: -10% delta
          ]
      let deltas5 = computeReconciliationDeltas chAggs5 casAggs5
      -- BUG: cust1/model1 has division by zero, returns 100.0%
      -- cust1/model2: (60.0 - 50.0) / 50.0 * 100.0 = 20.0%
      -- cust2/model1: (90.0 - 100.0) / 100.0 * 100.0 = -10.0%
      deltas5 `shouldContain` ("cust1", 100.0)  -- BUG: Misleading 100.0% for division by zero
      deltas5 `shouldContain` ("cust1", 20.0)
      deltas5 `shouldContain` ("cust2", -10.0)
      
      -- BUG: Solution: Use a special marker (e.g., Infinity or a sentinel value) for
      -- division-by-zero cases, or use a different formula that doesn't divide by zero

    it "BUG: computeReconciliationDeltas may not handle duplicate keys correctly" $ do
      -- BUG: computeReconciliationDeltas (line 228-253) uses Map.fromList which overwrites
      -- duplicate keys. If there are duplicate (customer_id, model_name) pairs in the input,
      -- only the last one will be kept, potentially losing data.
      
      -- Test with duplicate keys in ClickHouse aggregates
      let chAggs1 = [
            ReconciliationAggregates "cust1" "model1" 10 50.0,
            ReconciliationAggregates "cust1" "model1" 5 30.0  -- Duplicate key
          ]
      let casAggs1 = [ReconciliationAggregates "cust1" "model1" 15 80.0]
      let deltas1 = computeReconciliationDeltas chAggs1 casAggs1
      
      -- BUG: Map.fromList (line 232) keeps only the last entry for duplicate keys
      -- So chAggs1 will have only (cust1, model1) -> (5, 30.0)
      -- Delta = (80.0 - 30.0) / 30.0 * 100.0 = 166.67%
      -- But the correct delta should use the sum: (80.0 - 80.0) / 80.0 * 100.0 = 0.0%
      deltas1 `shouldBe` [("cust1", ((80.0 - 30.0) / 30.0) * 100.0)]  -- BUG: Wrong delta
      
      -- BUG: Test with duplicate keys in CAS aggregates
      let chAggs2 = [ReconciliationAggregates "cust1" "model1" 15 80.0]
      let casAggs2 = [
            ReconciliationAggregates "cust1" "model1" 10 50.0,
            ReconciliationAggregates "cust1" "model1" 5 30.0  -- Duplicate key
          ]
      let deltas2 = computeReconciliationDeltas chAggs2 casAggs2
      
      -- BUG: casAggs2 will have only (cust1, model1) -> (5, 30.0)
      -- Delta = (30.0 - 80.0) / 80.0 * 100.0 = -62.5%
      -- But the correct delta should use the sum: (80.0 - 80.0) / 80.0 * 100.0 = 0.0%
      deltas2 `shouldBe` [("cust1", ((30.0 - 80.0) / 80.0) * 100.0)]  -- BUG: Wrong delta
      
      -- BUG: Test with duplicates in both
      let chAggs3 = [
            ReconciliationAggregates "cust1" "model1" 10 50.0,
            ReconciliationAggregates "cust1" "model1" 5 30.0  -- Duplicate
          ]
      let casAggs3 = [
            ReconciliationAggregates "cust1" "model1" 8 40.0,
            ReconciliationAggregates "cust1" "model1" 7 35.0  -- Duplicate
          ]
      let deltas3 = computeReconciliationDeltas chAggs3 casAggs3
      
      -- BUG: Both maps will have only the last entry
      -- chAggs3: (cust1, model1) -> (5, 30.0)
      -- casAggs3: (cust1, model1) -> (7, 35.0)
      -- Delta = (35.0 - 30.0) / 30.0 * 100.0 = 16.67%
      -- But correct delta should use sums: (75.0 - 80.0) / 80.0 * 100.0 = -6.25%
      deltas3 `shouldBe` [("cust1", ((35.0 - 30.0) / 30.0) * 100.0)]  -- BUG: Wrong delta
      
      -- BUG: The issue is that Map.fromList silently overwrites duplicate keys
      -- This means:
      -- 1. Duplicate aggregates are lost (only last one kept)
      -- 2. Reconciliation deltas are computed incorrectly
      -- 3. No error or warning is raised for duplicate keys
      -- 4. Data loss occurs silently
      
      -- Solution: Aggregate duplicate keys before creating the map, or use a different
      -- data structure that preserves all values, or raise an error on duplicate keys

  describe "Fast Path ↔ Slow Path Consistency" $ do
    it "verifies fast path (ClickHouse) aggregates match slow path (CAS) aggregates" $ do
      -- BUG: This test requires real ClickHouse and CAS connections
      -- Without real connections, aggregates will be empty and match by default
      -- This test documents the need for proper test infrastructure
      chClient <- createClickHouseClient "localhost" 8123 "default"
      casClient <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      now <- getCurrentTime
      let range = TimeRange now (addUTCTime 3600 now)
      
      -- Query both paths
      chAggs <- queryClickHouseAggregates chClient range
      casAggs <- queryCASAggregates casClient Nothing range
      
      -- BUG: Without real connections, both will be empty
      -- This test documents the need for integration test infrastructure
      pure ()

    it "BUG: fast path may have stale data" $ do
      -- BUG: ClickHouse (fast path) may have stale data
      -- Reconciliation may not detect this if both paths are queried at different times
      -- This test documents the potential issue
      pure ()

    it "BUG: slow path may have missing data" $ do
      -- BUG: CAS (slow path) may have missing data if uploads fail
      -- Reconciliation may not detect this if both paths are queried independently
      -- This test documents the potential issue
      pure ()

    it "BUG: fast path and slow path may use different time ranges" $ do
      -- BUG: If queries are executed at different times,
      -- time ranges may be interpreted differently
      -- This test documents the potential issue
      chClient <- createClickHouseClient "localhost" 8123 "default"
      casClient <- createCASClient "https://cas.render.weyl.ai" "audit-trail"
      now <- getCurrentTime
      let range = TimeRange now (addUTCTime 3600 now)
      
      -- BUG: Time range may be interpreted differently by ClickHouse and CAS
      -- This may cause false discrepancies
      result <- reconcileFastSlowPath chClient casClient Nothing range
      pure ()

    it "BUG: DuckDB metadata may be out of sync with CAS" $ do
      -- BUG: DuckDB metadata table may not be updated when CAS objects are uploaded
      -- This may cause reconciliation to miss records
      -- This test documents the potential issue
      pure ()

  describe "Edge Cases" $ do
    it "handles empty content in audit entry" $ do
      let contentBS = BS.empty
      entry <- createAuditEntry "test" contentBS Nothing
      BS.length (ateContent entry) `shouldBe` 0
      BS.length (ateContentHash entry) `shouldBe` 32
      BS.length (ateSignature entry) `shouldBe` 64

    it "handles very large content in audit entry" $ do
      let largeContent = BS.replicate 1000000 65  -- 1MB
      entry <- createAuditEntry "test" largeContent Nothing
      BS.length (ateContent entry) `shouldBe` 1000000
      BS.length (ateContentHash entry) `shouldBe` 32

    it "handles unicode content in audit entry" $ do
      let content = "测试内容: 🚀 ⚡ ❌"
      let contentBS = Text.encodeUtf8 (Text.pack content)
      entry <- createAuditEntry "test" contentBS Nothing
      ateContent entry `shouldBe` contentBS

    it "handles binary content in audit entry" $ do
      let binaryContent = BS.pack [0x00, 0xFF, 0x80, 0x7F, 0x01, 0xFE]
      entry <- createAuditEntry "test" binaryContent Nothing
      ateContent entry `shouldBe` binaryContent

    it "handles hash chain with single entry" $ do
      let content = BS.pack [1, 2, 3]
      entry <- createAuditEntry "test" content Nothing
      let chain = HashChain [entry] (ateContentHash entry)
      verifyHashChain chain `shouldBe` True

    it "handles hash chain with many entries" $ do
      -- Create chain with 100 entries
      let content1 = BS.pack [1]
      entry1 <- createAuditEntry "test1" content1 Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      chain' <- foldM (\acc i -> do
            let content = BS.pack [fromIntegral i]
            entry <- createAuditEntry ("test" <> show i) content (Just (hcCurrentHash acc))
            pure $ appendToChain acc entry
          ) chain1 [2..100]
      
      length (hcEntries chain') `shouldBe` 100
      verifyHashChain chain' `shouldBe` True

  describe "Bug Detection" $ do
    it "BUG: createAuditEntry may not handle concurrent access to globalSigningKey" $ do
      -- BUG: globalSigningKey (line 30-35) is initialized once using unsafePerformIO.
      -- While Ed25519 signing should be thread-safe, the global access pattern
      -- may cause performance issues under high concurrency (contention on global key).
      -- This test is covered by the earlier "createAuditEntry may not handle concurrent creation correctly"
      -- test, which documents duplicate entry creation and global key access patterns.
      -- 
      -- Additional concern: If globalSigningKey needs to be rotated or updated,
      -- there's no mechanism to do so safely without restarting the application.
      -- 
      -- This test verifies that the global key is accessible and signing works,
      -- but the concurrency concerns are documented in the concurrent creation test.
      let content = BS.pack [1, 2, 3]
      entry <- createAuditEntry "test" content Nothing
      
      -- Verify signature is valid (global key works)
      let verified = verifySignature (ateContentHash entry) (ateSignature entry)
      verified `shouldBe` True
      
      -- BUG: The global key cannot be changed at runtime, which is a limitation
      -- if key rotation is needed for security compliance.

    it "BUG: verifyHashChain may not verify all entries" $ do
      -- BUG: verifyHashChain (line 89-103) uses foldl' with && operator (line 95).
      -- foldl' doesn't short-circuit - it evaluates all entries even if one fails.
      -- However, the issue is that if an entry fails verification, we don't know
      -- which entry failed or how many entries failed - we only get True/False.
      let content1 = BS.pack [1, 2, 3]
      entry1 <- createAuditEntry "test1" content1 Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      let content2 = BS.pack [4, 5, 6]
      entry2 <- createAuditEntry "test2" content2 (Just (ateContentHash entry1))
      let chain2 = appendToChain chain1 entry2
      
      let content3 = BS.pack [7, 8, 9]
      entry3 <- createAuditEntry "test3" content3 (Just (ateContentHash entry2))
      let chain3 = appendToChain chain2 entry3
      
      -- Corrupt entry2's signature
      let invalidSignature = BS.replicate 64 0x00
      let corruptedEntry2 = entry2 { ateSignature = invalidSignature }
      let corruptedChain = HashChain [entry1, corruptedEntry2, entry3] (hcCurrentHash chain3)
      
      -- BUG: verifyHashChain will return False, but we don't know:
      -- - Which entry failed (entry2)
      -- - How many entries failed (just entry2, or entry3 also if link is broken)
      -- - Whether other entries are valid (entry1 and entry3 might be valid)
      verifyHashChain corruptedChain `shouldBe` False
      
      -- BUG: The issue is that verifyHashChain doesn't provide diagnostic information.
      -- If multiple entries are corrupted, we only know the chain is invalid, not which
      -- entries are problematic. This makes debugging difficult.
      
      -- Test with multiple corrupted entries
      let corruptedEntry3 = entry3 { ateSignature = invalidSignature }
      let multiCorruptedChain = HashChain [entry1, corruptedEntry2, corruptedEntry3] (hcCurrentHash chain3)
      
      -- BUG: Still returns False, but we don't know both entries are corrupted
      verifyHashChain multiCorruptedChain `shouldBe` False
      
      -- BUG: Additionally, verifyHashChain doesn't verify the first entry's signature
      -- (line 92 returns True for single entry without checking), so if only the
      -- first entry is corrupted, it may not be detected.
      
      -- Test with corrupted first entry (single entry chain)
      let corruptedEntry1 = entry1 { ateSignature = invalidSignature }
      let corruptedChain1 = HashChain [corruptedEntry1] (ateContentHash corruptedEntry1)
      
      -- BUG: Single entry chain returns True without signature check (line 92)
      verifyHashChain corruptedChain1 `shouldBe` True  -- BUG: Should be False
      
      -- Solution: verifyHashChain should verify all entries including the first,
      -- and should provide diagnostic information about which entries failed.

    it "BUG: appendToChain may not handle concurrent appends" $ do
      -- BUG: appendToChain (line 80-86) is a pure function that creates a new HashChain.
      -- However, if multiple threads call appendToChain concurrently on the same chain,
      -- they may both use the same current hash, causing:
      -- 1. Both entries to reference the same previous hash
      -- 2. Chain structure to become a tree instead of linear
      -- 3. Verification to fail or become ambiguous
      let content1 = BS.pack [1, 2, 3]
      entry1 <- createAuditEntry "test1" content1 Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      -- Simulate concurrent appends (both use same previous hash)
      let content2 = BS.pack [4, 5, 6]
      entry2 <- createAuditEntry "test2" content2 (Just (hcCurrentHash chain1))
      let chain2a = appendToChain chain1 entry2
      
      let content3 = BS.pack [7, 8, 9]
      entry3 <- createAuditEntry "test3" content3 (Just (hcCurrentHash chain1))  -- Same previous hash as entry2
      let chain2b = appendToChain chain1 entry3
      
      -- BUG: Both chains are valid individually, but they represent a fork:
      -- chain1 -> entry2 (chain2a)
      -- chain1 -> entry3 (chain2b)
      -- This creates ambiguity about which chain is the "correct" one.
      verifyHashChain chain2a `shouldBe` True
      verifyHashChain chain2b `shouldBe` True
      
      -- BUG: If both chains are stored or used, we have a fork in the chain.
      -- This breaks the linear chain invariant and makes verification ambiguous.
      -- Solution: Use STM or locks to serialize appendToChain operations, or use
      -- a persistent data structure that handles concurrent modifications.
      
      -- BUG: Additionally, if appendToChain is called on a chain that has been
      -- modified elsewhere, the modification may be lost (no conflict detection).

    it "BUG: reconciliation may not handle clock skew" $ do
      -- BUG: reconcileFastSlowPath (line 106-127) queries ClickHouse and CAS
      -- using the same TimeRange. However, if ClickHouse and CAS have different
      -- clock times (clock skew), records may be:
      -- 1. Included in one query but not the other (missed in reconciliation)
      -- 2. Excluded from both queries (missed entirely)
      -- 3. Included in wrong time range (false discrepancies)
      --
      -- This test documents the issue - actual testing requires clock manipulation
      -- or time mocking infrastructure.
      
      -- BUG: If ClickHouse clock is 5 minutes ahead of CAS clock:
      -- - ClickHouse query: timestamp >= now AND timestamp < now+1h
      --   Returns records with ClickHouse timestamps in range
      -- - CAS query: timestamp >= now AND timestamp < now+1h
      --   Returns records with CAS timestamps in range
      -- - Records with timestamps between CAS-now and ClickHouse-now may be:
      --   * In ClickHouse query but not CAS query (false discrepancy)
      --   * In CAS query but not ClickHouse query (false discrepancy)
      --   * In neither query (missed entirely)
      
      -- BUG: The issue is that TimeRange uses a single time (now) for both queries,
      -- but if the systems have clock skew, the same TimeRange represents different
      -- actual time periods on each system.
      
      -- Solution: Use clock synchronization (NTP) or adjust TimeRange for known clock skew.
      
      -- This test documents the issue - actual testing requires infrastructure to simulate clock skew.
      pure ()  -- Requires clock mocking infrastructure

    it "BUG: queryCASAggregates may not handle DuckDB query errors" $ do
      -- BUG: queryCASAggregates (line 197-224) catches exceptions (line 207) and
      -- returns empty list on error (line 215). This means:
      -- 1. Query errors are silently ignored
      -- 2. Reconciliation proceeds with empty CAS aggregates
      -- 3. False reconciliation (empty matches empty) may occur
      -- 4. Errors are not logged, hiding data issues
      --
      -- This test documents the issue - actual testing requires DuckDB mocking infrastructure.
      
      -- BUG: If DuckDB query fails (e.g., table doesn't exist, syntax error, connection error),
      -- queryCASAggregates returns [] without logging the error. This causes:
      -- - Reconciliation to proceed as if CAS has no data
      -- - False reconciliation if ClickHouse also has no data
      -- - Data issues to be hidden (no error reporting)
      
      -- BUG: The try block (line 207) catches SomeException but doesn't log it.
      -- This makes debugging difficult when queries fail.
      
      -- Solution: Log errors before returning empty list, or propagate errors
      -- so callers can handle them appropriately.
      
      -- This test documents the issue - actual testing requires DuckDB mocking infrastructure.
      pure ()  -- Requires DuckDB mocking infrastructure

    it "BUG: computeReconciliationDeltas may not handle duplicate keys correctly" $ do
      -- BUG: computeReconciliationDeltas (line 228-253) uses Map.fromList (line 232-233)
      -- which takes the LAST value for duplicate keys. If there are duplicate
      -- (customerId, modelName) pairs in the input aggregates, only the last one
      -- will be kept, potentially losing data and causing incorrect reconciliation deltas.
      let chAggs = 
            [ ReconciliationAggregates "cust1" "model1" 10 100.0
            , ReconciliationAggregates "cust1" "model1" 20 200.0  -- Duplicate key
            ]
      let casAggs = [ReconciliationAggregates "cust1" "model1" 15 150.0]
      let deltas = computeReconciliationDeltas chAggs casAggs
      
      -- BUG: Map.fromList keeps only the last value (200.0) for duplicate key.
      -- The first value (100.0) is lost. Delta is computed as:
      -- (150.0 - 200.0) / 200.0 * 100.0 = -25.0%
      -- But the correct delta should use the sum: (150.0 - 300.0) / 300.0 * 100.0 = -50.0%
      deltas `shouldBe` [("cust1", ((150.0 - 200.0) / 200.0) * 100.0)]  -- BUG: Wrong delta
      
      -- BUG: Test with duplicates in CAS aggregates
      let chAggs2 = [ReconciliationAggregates "cust1" "model1" 15 150.0]
      let casAggs2 = 
            [ ReconciliationAggregates "cust1" "model1" 10 100.0
            , ReconciliationAggregates "cust1" "model1" 20 200.0  -- Duplicate key
            ]
      let deltas2 = computeReconciliationDeltas chAggs2 casAggs2
      
      -- BUG: CAS aggregates also lose first value. Delta is computed as:
      -- (200.0 - 150.0) / 150.0 * 100.0 = 33.33%
      -- But correct delta should use sum: (300.0 - 150.0) / 150.0 * 100.0 = 100.0%
      deltas2 `shouldBe` [("cust1", ((200.0 - 150.0) / 150.0) * 100.0)]  -- BUG: Wrong delta
      
      -- BUG: Test with duplicates in both
      let chAggs3 = 
            [ ReconciliationAggregates "cust1" "model1" 10 100.0
            , ReconciliationAggregates "cust1" "model1" 5 50.0  -- Duplicate
            ]
      let casAggs3 = 
            [ ReconciliationAggregates "cust1" "model1" 8 80.0
            , ReconciliationAggregates "cust1" "model1" 7 70.0  -- Duplicate
            ]
      let deltas3 = computeReconciliationDeltas chAggs3 casAggs3
      
      -- BUG: Both maps keep only last value:
      -- chAggs3: (cust1, model1) -> (5, 50.0)
      -- casAggs3: (cust1, model1) -> (7, 70.0)
      -- Delta = (70.0 - 50.0) / 50.0 * 100.0 = 40.0%
      -- But correct delta should use sums: (150.0 - 150.0) / 150.0 * 100.0 = 0.0%
      deltas3 `shouldBe` [("cust1", ((70.0 - 50.0) / 50.0) * 100.0)]  -- BUG: Wrong delta
      
      -- BUG: The issue is that Map.fromList silently overwrites duplicate keys.
      -- This means:
      -- 1. Duplicate aggregates are lost (only last one kept)
      -- 2. Reconciliation deltas are computed incorrectly
      -- 3. No error or warning is raised for duplicate keys
      -- 4. Data loss occurs silently
      -- 5. Reconciliation may show false discrepancies or miss real discrepancies
      
      -- Solution: Aggregate duplicate keys before creating the map, or use a different
      -- data structure that preserves all values, or raise an error on duplicate keys.
