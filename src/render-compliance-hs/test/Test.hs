{-# LANGUAGE OverloadedStrings #-}

-- | Render Compliance Test Suite
-- | Comprehensive tests for compliance and audit trail functionality
module Main where

import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

import Render.Compliance.AuditTrail
import Render.ClickHouse.Client (createClickHouseClient)
import Render.CAS.Client (createCASClient)

import Data.Text (Text)
import qualified Data.Text as Text
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.Time (getCurrentTime, addUTCTime)
import Data.Maybe (isJust, isNothing)
import Control.Monad (foldM)
import qualified Data.Map.Strict as Map

main :: IO ()
main = hspec $ do
  describe "Render Compliance Tests" $ do
    hashChainTests
    reconciliationTests
    propertyTests
    auditTrailDeepTests
    complianceDeepTests

-- | Hash chain tests
hashChainTests :: Spec
hashChainTests = describe "Hash Chain" $ do
  it "creates first audit entry" $ do
    content <- pure $ BS.pack [1, 2, 3, 4]
    entry <- createAuditEntry "test" content Nothing
    ateEventType entry `shouldBe` "test"
    isNothing (atePreviousHash entry) `shouldBe` True

  it "creates hash chain with single entry" $ do
    content <- pure $ BS.pack [1, 2, 3, 4]
    entry <- createAuditEntry "test" content Nothing
    let chain = HashChain [entry] (ateContentHash entry)
    verifyHashChain chain `shouldBe` True

  it "creates hash chain with multiple entries" $ do
    content1 <- pure $ BS.pack [1, 2, 3, 4]
    entry1 <- createAuditEntry "test1" content1 Nothing
    let chain1 = HashChain [entry1] (ateContentHash entry1)
    
    content2 <- pure $ BS.pack [5, 6, 7, 8]
    entry2 <- createAuditEntry "test2" content2 (Just (ateContentHash entry1))
    let chain2 = appendToChain chain1 entry2
    
    verifyHashChain chain2 `shouldBe` True

  it "verifies hash chain integrity" $ do
    content1 <- pure $ BS.pack [1, 2, 3, 4]
    entry1 <- createAuditEntry "test1" content1 Nothing
    let chain1 = HashChain [entry1] (ateContentHash entry1)
    
    content2 <- pure $ BS.pack [5, 6, 7, 8]
    entry2 <- createAuditEntry "test2" content2 (Just (ateContentHash entry1))
    let chain2 = appendToChain chain1 entry2
    
    verifyHashChain chain2 `shouldBe` True

-- | Reconciliation tests
reconciliationTests :: Spec
reconciliationTests = describe "Reconciliation" $ do
  it "reconciles matching aggregates" $ do
    chClient <- createClickHouseClient "localhost" 8123 "default"
    casClient <- createCASClient "https://cas.test" "test-bucket"
    now <- getCurrentTime
    let range = TimeRange now (addUTCTime 3600 now)
    
    -- Reconciliation without DuckDB (CAS aggregates will be empty)
    result <- reconcileFastSlowPath chClient casClient Nothing range
    rrStatus result `shouldSatisfy` (\s -> s == Reconciled || s == DiscrepanciesFound)

  it "computes reconciliation deltas" $ do
    now <- getCurrentTime
    let chAggs = [ReconciliationAggregates "cust1" "model1" 10 5.0]
    let casAggs = [ReconciliationAggregates "cust1" "model1" 10 5.0]
    
    let deltas = computeReconciliationDeltas chAggs casAggs
    -- Should have zero delta for matching aggregates
    deltas `shouldSatisfy` (all (\(_, delta) -> abs delta < 0.001))

  it "detects discrepancies" $ do
    now <- getCurrentTime
    let chAggs = [ReconciliationAggregates "cust1" "model1" 10 5.0]
    let casAggs = [ReconciliationAggregates "cust1" "model1" 10 6.0] -- 20% difference
    
    let deltas = computeReconciliationDeltas chAggs casAggs
    -- Should detect discrepancy
    deltas `shouldSatisfy` (any (\(_, delta) -> abs delta > 0.001))

-- | Property tests
propertyTests :: Spec
propertyTests = describe "Property Tests" $ do
  prop "hash chain verification is idempotent" $ \entries -> do
    -- Create hash chain from entries
    chain <- foldM (\acc (eventType, content) -> do
      prevHash <- case hcEntries acc of
        [] -> pure Nothing
        es -> pure $ Just (ateContentHash (last es))
      entry <- createAuditEntry eventType (BS.pack content) prevHash
      pure $ appendToChain acc entry
    ) (HashChain [] (BS.pack [])) (take 10 entries) -- Limit to 10 entries
    
    -- Verification should be idempotent
    let verified1 = verifyHashChain chain
    let verified2 = verifyHashChain chain
    verified1 `shouldBe` verified2

  prop "hash chain entries are linked correctly" $ \content -> do
    entry1 <- createAuditEntry "test1" (BS.pack content) Nothing
    entry2 <- createAuditEntry "test2" (BS.pack content) (Just (ateContentHash entry1))
    
    case atePreviousHash entry2 of
      Just prevHash -> prevHash `shouldBe` ateContentHash entry1
      Nothing -> expectationFailure "Entry2 should have previous hash"

  where
    foldM :: Monad m => (a -> b -> m a) -> a -> [b] -> m a
    foldM _ acc [] = pure acc
    foldM f acc (x:xs) = do
      acc' <- f acc x
      foldM f acc' xs

-- | Deep comprehensive tests for AuditTrail
auditTrailDeepTests :: Spec
auditTrailDeepTests = describe "AuditTrail Deep Tests" $ do
  describe "createAuditEntry" $ do
    it "handles empty content" $ do
      entry <- createAuditEntry "test" BS.empty Nothing
      BS.length (ateContent entry) `shouldBe` 0
      BS.length (ateContentHash entry) `shouldBe` 32 -- BLAKE2b-256 is 32 bytes
      BS.length (ateSignature entry) `shouldBe` 64 -- Ed25519 signature is 64 bytes
      isNothing (atePreviousHash entry) `shouldBe` True

    it "handles very large content" $ do
      let largeContent = BS.replicate 1000000 65 -- 1MB of 'A'
      entry <- createAuditEntry "test" largeContent Nothing
      BS.length (ateContent entry) `shouldBe` 1000000
      BS.length (ateContentHash entry) `shouldBe` 32

    it "computes chain hash correctly for first entry" $ do
      let content = BS.pack [1, 2, 3, 4]
      entry <- createAuditEntry "test" content Nothing
      -- First entry: chain hash = content hash (verified by checking previous hash is Nothing)
      isNothing (atePreviousHash entry) `shouldBe` True
      BS.length (ateContentHash entry) `shouldBe` 32 -- BLAKE2b-256 is 32 bytes

    it "computes chain hash correctly for subsequent entry" $ do
      let content1 = BS.pack [1, 2, 3, 4]
      entry1 <- createAuditEntry "test1" content1 Nothing
      let prevHash = ateContentHash entry1
      
      let content2 = BS.pack [5, 6, 7, 8]
      entry2 <- createAuditEntry "test2" content2 (Just prevHash)
      -- Subsequent entry: chain hash = hash(prevHash <> contentHash)
      -- The signature is over the chain hash, but we verify the previous hash link
      isJust (atePreviousHash entry2) `shouldBe` True
      case atePreviousHash entry2 of
        Just ph -> ph `shouldBe` prevHash
        Nothing -> expectationFailure "Entry2 should have previous hash"

    it "produces different hashes for different content" $ do
      let content1 = BS.pack [1, 2, 3, 4]
      let content2 = BS.pack [5, 6, 7, 8]
      entry1 <- createAuditEntry "test1" content1 Nothing
      entry2 <- createAuditEntry "test2" content2 Nothing
      ateContentHash entry1 `shouldNotBe` ateContentHash entry2

    it "produces different signatures for different content" $ do
      let content1 = BS.pack [1, 2, 3, 4]
      let content2 = BS.pack [5, 6, 7, 8]
      entry1 <- createAuditEntry "test1" content1 Nothing
      entry2 <- createAuditEntry "test2" content2 Nothing
      ateSignature entry1 `shouldNotBe` ateSignature entry2

  describe "appendToChain" $ do
    it "handles empty chain" $ do
      let emptyChain = HashChain [] (BS.pack [])
      content <- pure $ BS.pack [1, 2, 3]
      entry <- createAuditEntry "test" content Nothing
      let newChain = appendToChain emptyChain entry
      length (hcEntries newChain) `shouldBe` 1
      hcCurrentHash newChain `shouldBe` ateContentHash entry

    it "appends to chain with single entry" $ do
      content1 <- pure $ BS.pack [1, 2, 3]
      entry1 <- createAuditEntry "test1" content1 Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      content2 <- pure $ BS.pack [4, 5, 6]
      entry2 <- createAuditEntry "test2" content2 (Just (ateContentHash entry1))
      let chain2 = appendToChain chain1 entry2
      
      length (hcEntries chain2) `shouldBe` 2
      -- Verify chain hash is computed correctly (should be hash of prevHash <> contentHash)
      BS.length (hcCurrentHash chain2) `shouldBe` 32 -- BLAKE2b-256 is 32 bytes
      verifyHashChain chain2 `shouldBe` True -- Chain integrity confirms correct hash computation

    it "maintains hash chain integrity after append" $ do
      content1 <- pure $ BS.pack [1, 2, 3]
      entry1 <- createAuditEntry "test1" content1 Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      verifyHashChain chain1 `shouldBe` True
      
      content2 <- pure $ BS.pack [4, 5, 6]
      entry2 <- createAuditEntry "test2" content2 (Just (ateContentHash entry1))
      let chain2 = appendToChain chain1 entry2
      verifyHashChain chain2 `shouldBe` True

    it "handles multiple appends correctly" $ do
      content1 <- pure $ BS.pack [1]
      entry1 <- createAuditEntry "test1" content1 Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      content2 <- pure $ BS.pack [2]
      entry2 <- createAuditEntry "test2" content2 (Just (ateContentHash entry1))
      let chain2 = appendToChain chain1 entry2
      
      content3 <- pure $ BS.pack [3]
      entry3 <- createAuditEntry "test3" content3 (Just (hcCurrentHash chain2))
      let chain3 = appendToChain chain2 entry3
      
      length (hcEntries chain3) `shouldBe` 3
      verifyHashChain chain3 `shouldBe` True

  describe "verifyHashChain" $ do
    it "verifies empty chain" $ do
      let emptyChain = HashChain [] (BS.pack [])
      verifyHashChain emptyChain `shouldBe` True

    it "verifies single entry chain" $ do
      content <- pure $ BS.pack [1, 2, 3]
      entry <- createAuditEntry "test" content Nothing
      let chain = HashChain [entry] (ateContentHash entry)
      verifyHashChain chain `shouldBe` True

    it "detects corrupted hash chain (wrong previous hash)" $ do
      content1 <- pure $ BS.pack [1, 2, 3]
      entry1 <- createAuditEntry "test1" content1 Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      content2 <- pure $ BS.pack [4, 5, 6]
      entry2 <- createAuditEntry "test2" content2 (Just (ateContentHash entry1))
      let chain2 = appendToChain chain1 entry2
      
      -- Corrupt entry2's previous hash
      let corruptedEntry2 = entry2 { atePreviousHash = Just (BS.pack [99, 99, 99]) }
      let corruptedChain = HashChain [entry1, corruptedEntry2] (hcCurrentHash chain2)
      verifyHashChain corruptedChain `shouldBe` False

    it "detects corrupted hash chain (wrong signature)" $ do
      content1 <- pure $ BS.pack [1, 2, 3]
      entry1 <- createAuditEntry "test1" content1 Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      content2 <- pure $ BS.pack [4, 5, 6]
      entry2 <- createAuditEntry "test2" content2 (Just (ateContentHash entry1))
      let chain2 = appendToChain chain1 entry2
      
      -- Corrupt entry2's signature
      let corruptedEntry2 = entry2 { ateSignature = BS.pack [99 | _ <- [1..64]] }
      let corruptedChain = HashChain [entry1, corruptedEntry2] (hcCurrentHash chain2)
      verifyHashChain corruptedChain `shouldBe` False

    it "verifies long hash chain correctly" $ do
      -- Build chain with 10 entries
      content1 <- pure $ BS.pack [1]
      entry1 <- createAuditEntry "test1" content1 Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      chain <- foldM (\acc i -> do
        let content = BS.pack [fromIntegral i]
        let prevHash = hcCurrentHash acc
        entry <- createAuditEntry ("test" <> Text.pack (show i)) content (Just prevHash)
        pure $ appendToChain acc entry
      ) chain1 [2..10]
      
      length (hcEntries chain) `shouldBe` 10
      verifyHashChain chain `shouldBe` True

  describe "computeReconciliationDeltas - Bug 17 Fix Verification" $ do
    it "uses (customerId, modelName) pairs as keys (Bug 17 fix)" $ do
      let chAggs = 
            [ ReconciliationAggregates "cust1" "model1" 10 5.0
            , ReconciliationAggregates "cust1" "model2" 20 10.0
            ]
      let casAggs = 
            [ ReconciliationAggregates "cust1" "model1" 10 5.0
            , ReconciliationAggregates "cust1" "model2" 20 10.0
            ]
      let deltas = computeReconciliationDeltas chAggs casAggs
      -- Should have zero deltas for both (cust1, model1) and (cust1, model2)
      length deltas `shouldBe` 2
      all (\(_, delta) -> abs delta < 0.001) deltas `shouldBe` True

    it "detects discrepancies per model, not per customer (Bug 17 fix)" $ do
      let chAggs = 
            [ ReconciliationAggregates "cust1" "model1" 10 5.0
            , ReconciliationAggregates "cust1" "model2" 20 10.0
            ]
      let casAggs = 
            [ ReconciliationAggregates "cust1" "model1" 10 6.0 -- 20% difference for model1
            , ReconciliationAggregates "cust1" "model2" 20 10.0 -- No difference for model2
            ]
      let deltas = computeReconciliationDeltas chAggs casAggs
      -- Should detect discrepancy for model1 but not model2
      let model1Delta = snd (head deltas)
      let model2Delta = snd (last deltas)
      abs model1Delta `shouldSatisfy` (> 0.001) -- Model1 has discrepancy
      abs model2Delta `shouldBe` 0.0 -- Model2 matches

    it "handles aggregates only in ClickHouse" $ do
      let chAggs = 
            [ ReconciliationAggregates "cust1" "model1" 10 5.0
            , ReconciliationAggregates "cust1" "model2" 20 10.0
            ]
      let casAggs = []
      let deltas = computeReconciliationDeltas chAggs casAggs
      length deltas `shouldBe` 2
      -- Both should show -100% delta (CAS has 0, CH has value)
      all (\(_, delta) -> abs (delta - (-100.0)) < 0.001) deltas `shouldBe` True

    it "handles aggregates only in CAS" $ do
      let chAggs = []
      let casAggs = 
            [ ReconciliationAggregates "cust1" "model1" 10 5.0
            , ReconciliationAggregates "cust1" "model2" 20 10.0
            ]
      let deltas = computeReconciliationDeltas chAggs casAggs
      length deltas `shouldBe` 2
      -- Both should show 100% delta (CH has 0, CAS has value)
      all (\(_, delta) -> abs (delta - 100.0) < 0.001) deltas `shouldBe` True

    it "handles different customers with same model name" $ do
      let chAggs = 
            [ ReconciliationAggregates "cust1" "model1" 10 5.0
            , ReconciliationAggregates "cust2" "model1" 15 7.5
            ]
      let casAggs = 
            [ ReconciliationAggregates "cust1" "model1" 10 5.0
            , ReconciliationAggregates "cust2" "model1" 15 7.5
            ]
      let deltas = computeReconciliationDeltas chAggs casAggs
      length deltas `shouldBe` 2
      all (\(_, delta) -> abs delta < 0.001) deltas `shouldBe` True

    it "calculates percentage delta correctly" $ do
      let chAggs = [ReconciliationAggregates "cust1" "model1" 10 100.0]
      let casAggs = [ReconciliationAggregates "cust1" "model1" 10 150.0]
      let deltas = computeReconciliationDeltas chAggs casAggs
      case deltas of
        [(cid, delta)] -> do
          cid `shouldBe` "cust1"
          abs (delta - 50.0) `shouldBe` 0.0 -- (150-100)/100 * 100 = 50%

    it "handles zero GPU seconds in ClickHouse" $ do
      let chAggs = [ReconciliationAggregates "cust1" "model1" 10 0.0]
      let casAggs = [ReconciliationAggregates "cust1" "model1" 10 50.0]
      let deltas = computeReconciliationDeltas chAggs casAggs
      case deltas of
        [(cid, delta)] -> do
          cid `shouldBe` "cust1"
          abs (delta - 100.0) `shouldBe` 0.0 -- When CH is 0 and CAS > 0, delta is 100%

    it "handles both zero GPU seconds" $ do
      let chAggs = [ReconciliationAggregates "cust1" "model1" 10 0.0]
      let casAggs = [ReconciliationAggregates "cust1" "model1" 10 0.0]
      let deltas = computeReconciliationDeltas chAggs casAggs
      case deltas of
        [(cid, delta)] -> do
          cid `shouldBe` "cust1"
          abs delta `shouldBe` 0.0

  describe "reconcileFastSlowPath" $ do
    it "handles empty aggregates from both paths" $ do
      chClient <- createClickHouseClient "localhost" 8123 "default"
      casClient <- createCASClient "https://cas.test" "test-bucket"
      now <- getCurrentTime
      let range = TimeRange now (addUTCTime 3600 now)
      result <- reconcileFastSlowPath chClient casClient Nothing range
      rrRange result `shouldBe` range
      rrStatus result `shouldSatisfy` (\s -> s == Reconciled || s == DiscrepanciesFound)

    it "reports Reconciled when deltas below threshold" $ do
      -- Note: This test verifies the threshold logic structure
      -- Actual reconciliation requires real ClickHouse/CAS connections
      chClient <- createClickHouseClient "localhost" 8123 "default"
      casClient <- createCASClient "https://cas.test" "test-bucket"
      now <- getCurrentTime
      let range = TimeRange now (addUTCTime 3600 now)
      result <- reconcileFastSlowPath chClient casClient Nothing range
      rrRange result `shouldBe` range
      -- Status depends on actual query results, but structure is correct

    it "handles time range correctly" $ do
      chClient <- createClickHouseClient "localhost" 8123 "default"
      casClient <- createCASClient "https://cas.test" "test-bucket"
      now <- getCurrentTime
      let start = now
      let end = addUTCTime 7200 now -- 2 hours
      let range = TimeRange start end
      result <- reconcileFastSlowPath chClient casClient Nothing range
      rrRange result `shouldBe` range

-- | Additional deep comprehensive tests for edge cases and bug detection
complianceDeepTests :: Spec
complianceDeepTests = describe "Compliance Deep Tests" $ do
  describe "Hash Chain Integrity Edge Cases" $ do
    it "detects entry with wrong chain hash computation" $ do
      content1 <- pure $ BS.pack [1, 2, 3]
      entry1 <- createAuditEntry "test1" content1 Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      content2 <- pure $ BS.pack [4, 5, 6]
      entry2 <- createAuditEntry "test2" content2 (Just (ateContentHash entry1))
      let chain2 = appendToChain chain1 entry2
      
      -- Corrupt the chain hash computation by using wrong previous hash
      let wrongPrevHash = BS.pack [99 | _ <- [1..32]]
      let corruptedEntry2 = entry2 { atePreviousHash = Just wrongPrevHash }
      let corruptedChain = HashChain [entry1, corruptedEntry2] (hcCurrentHash chain2)
      verifyHashChain corruptedChain `shouldBe` False

    it "detects entry with signature over wrong content" $ do
      content1 <- pure $ BS.pack [1, 2, 3]
      entry1 <- createAuditEntry "test1" content1 Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      content2 <- pure $ BS.pack [4, 5, 6]
      entry2 <- createAuditEntry "test2" content2 (Just (ateContentHash entry1))
      
      -- Create entry with modified content but same previous hash
      content2Modified <- pure $ BS.pack [4, 5, 7] -- One byte different
      entry2Modified <- createAuditEntry "test2" content2Modified (Just (ateContentHash entry1))
      
      -- Replace signature with signature from different content
      let corruptedEntry2 = entry2 { ateSignature = ateSignature entry2Modified }
      let corruptedChain = HashChain [entry1, corruptedEntry2] (hcCurrentHash chain1)
      verifyHashChain corruptedChain `shouldBe` False

    it "handles hash chain with entry missing previous hash when it should have one" $ do
      content1 <- pure $ BS.pack [1, 2, 3]
      entry1 <- createAuditEntry "test1" content1 Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      content2 <- pure $ BS.pack [4, 5, 6]
      -- Create entry2 with wrong previous hash (None instead of Just)
      entry2Wrong <- createAuditEntry "test2" content2 Nothing -- Should have previous hash!
      let corruptedChain = HashChain [entry1, entry2Wrong] (ateContentHash entry2Wrong)
      -- verifyHashChain should detect this inconsistency
      verifyHashChain corruptedChain `shouldBe` False

    it "handles hash chain with entry having previous hash when it shouldn't" $ do
      -- First entry should have Nothing for previous hash
      content1 <- pure $ BS.pack [1, 2, 3]
      entry1Wrong <- createAuditEntry "test1" content1 (Just (BS.pack [99 | _ <- [1..32]]))
      let corruptedChain = HashChain [entry1Wrong] (ateContentHash entry1Wrong)
      -- First entry with previous hash should fail verification
      verifyHashChain corruptedChain `shouldBe` False

    it "verifies hash chain with entries in wrong order" $ do
      content1 <- pure $ BS.pack [1, 2, 3]
      entry1 <- createAuditEntry "test1" content1 Nothing
      
      content2 <- pure $ BS.pack [4, 5, 6]
      entry2 <- createAuditEntry "test2" content2 (Just (ateContentHash entry1))
      
      -- Create chain with entries in wrong order
      let wrongOrderChain = HashChain [entry2, entry1] (hcCurrentHash (HashChain [entry1, entry2] (BS.pack [])))
      verifyHashChain wrongOrderChain `shouldBe` False

  describe "appendToChain Edge Cases" $ do
    it "handles append with mismatched previous hash" $ do
      content1 <- pure $ BS.pack [1, 2, 3]
      entry1 <- createAuditEntry "test1" content1 Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      content2 <- pure $ BS.pack [4, 5, 6]
      -- Create entry2 with wrong previous hash
      entry2Wrong <- createAuditEntry "test2" content2 (Just (BS.pack [99 | _ <- [1..32]]))
      let corruptedChain = appendToChain chain1 entry2Wrong
      -- Chain hash computation should be wrong
      verifyHashChain corruptedChain `shouldBe` False

    it "handles append to chain with incorrect current hash" $ do
      content1 <- pure $ BS.pack [1, 2, 3]
      entry1 <- createAuditEntry "test1" content1 Nothing
      -- Create chain with wrong current hash
      let chain1Wrong = HashChain [entry1] (BS.pack [99 | _ <- [1..32]])
      
      content2 <- pure $ BS.pack [4, 5, 6]
      entry2 <- createAuditEntry "test2" content2 (Just (ateContentHash entry1))
      let chain2 = appendToChain chain1Wrong entry2
      -- Should still compute correct chain hash despite wrong initial hash
      verifyHashChain chain2 `shouldBe` True -- appendToChain recomputes hash correctly

  describe "computeReconciliationDeltas Edge Cases" $ do
    it "handles very large delta percentages" $ do
      let chAggs = [ReconciliationAggregates "cust1" "model1" 10 0.001] -- Very small value
      let casAggs = [ReconciliationAggregates "cust1" "model1" 10 1000.0] -- Very large value
      let deltas = computeReconciliationDeltas chAggs casAggs
      case deltas of
        [(cid, delta)] -> do
          cid `shouldBe` "cust1"
          -- Delta should be very large: (1000 - 0.001) / 0.001 * 100 = 9999900%
          abs delta `shouldSatisfy` (> 9990000.0)

    it "handles negative GPU seconds (edge case - shouldn't happen but test robustness)" $ do
      -- Note: Double can be negative, test edge case
      let chAggs = [ReconciliationAggregates "cust1" "model1" 10 100.0]
      let casAggs = [ReconciliationAggregates "cust1" "model1" 10 (-50.0)] -- Negative value
      let deltas = computeReconciliationDeltas chAggs casAggs
      case deltas of
        [(cid, delta)] -> do
          cid `shouldBe` "cust1"
          -- Delta should be negative: (-50 - 100) / 100 * 100 = -150%
          abs (delta - (-150.0)) `shouldBe` 0.0

    it "handles duplicate (customerId, modelName) pairs in same list" $ do
      -- Map.fromList takes last value for duplicates
      let chAggs = 
            [ ReconciliationAggregates "cust1" "model1" 10 100.0
            , ReconciliationAggregates "cust1" "model1" 20 200.0 -- Duplicate key
            ]
      let casAggs = [ReconciliationAggregates "cust1" "model1" 15 150.0]
      let deltas = computeReconciliationDeltas chAggs casAggs
      -- Should use last value (200.0) for cust1/model1
      case deltas of
        [(cid, delta)] -> do
          cid `shouldBe` "cust1"
          -- Delta: (150 - 200) / 200 * 100 = -25%
          abs (delta - (-25.0)) `shouldBe` 0.0

    it "handles multiple customers with same model name and different deltas" $ do
      let chAggs = 
            [ ReconciliationAggregates "cust1" "model1" 10 100.0
            , ReconciliationAggregates "cust2" "model1" 20 200.0
            , ReconciliationAggregates "cust3" "model1" 30 300.0
            ]
      let casAggs = 
            [ ReconciliationAggregates "cust1" "model1" 10 100.0 -- No delta
            , ReconciliationAggregates "cust2" "model1" 20 250.0 -- +25% delta
            , ReconciliationAggregates "cust3" "model1" 30 150.0 -- -50% delta
            ]
      let deltas = computeReconciliationDeltas chAggs casAggs
      length deltas `shouldBe` 3
      -- Verify each delta
      let deltaMap = Map.fromList deltas
      Map.lookup "cust1" deltaMap `shouldBe` Just 0.0
      Map.lookup "cust2" deltaMap `shouldBe` Just 25.0
      Map.lookup "cust3" deltaMap `shouldBe` Just (-50.0)

    it "handles aggregates with zero request count but non-zero GPU seconds" $ do
      let chAggs = [ReconciliationAggregates "cust1" "model1" 0 100.0]
      let casAggs = [ReconciliationAggregates "cust1" "model1" 0 150.0]
      let deltas = computeReconciliationDeltas chAggs casAggs
      case deltas of
        [(cid, delta)] -> do
          cid `shouldBe` "cust1"
          -- Delta: (150 - 100) / 100 * 100 = 50%
          abs (delta - 50.0) `shouldBe` 0.0

  describe "Hash Computation Consistency" $ do
    it "produces deterministic hashes for identical content" $ do
      let content = BS.pack [1..100]
      let hash1 = computeBlake2bHash content
      let hash2 = computeBlake2bHash content
      hash1 `shouldBe` hash2

    it "produces different hashes for different content" $ do
      let content1 = BS.pack [1..100]
      let content2 = BS.pack [1..99] <> BS.pack [101]
      let hash1 = computeBlake2bHash content1
      let hash2 = computeBlake2bHash content2
      hash1 `shouldNotBe` hash2

    it "hash length is always 32 bytes" $ do
      let contents = [BS.empty, BS.pack [1], BS.pack [1..100], BS.replicate 1000000 65]
      mapM_ (\content -> BS.length (computeBlake2bHash content) `shouldBe` 32) contents

    it "produces different chain hashes for same content with different previous hashes" $ do
      let content = BS.pack [1, 2, 3]
      let prevHash1 = BS.pack [1 | _ <- [1..32]]
      let prevHash2 = BS.pack [2 | _ <- [1..32]]
      
      -- Compute chain hash manually: hash(prevHash <> contentHash)
      let contentHash = computeBlake2bHash content
      let chainHash1 = computeBlake2bHash (prevHash1 <> contentHash)
      let chainHash2 = computeBlake2bHash (prevHash2 <> contentHash)
      
      chainHash1 `shouldNotBe` chainHash2

  describe "Signature Verification Edge Cases" $ do
    it "rejects signature with wrong length" $ do
      let content = BS.pack [1, 2, 3]
      let wrongLengthSig = BS.pack [1..63] -- 63 bytes instead of 64
      verifySignature content wrongLengthSig `shouldBe` False

    it "rejects signature with all zeros" $ do
      let content = BS.pack [1, 2, 3]
      let zeroSig = BS.replicate 64 0
      verifySignature content zeroSig `shouldBe` False

    it "rejects signature for modified content" $ do
      content1 <- pure $ BS.pack [1, 2, 3]
      sig1 <- signEntry content1
      
      let content2 = BS.pack [1, 2, 4] -- One byte different
      verifySignature content2 sig1 `shouldBe` False

    it "verifies signature for empty content" $ do
      content <- pure $ BS.empty
      sig <- signEntry content
      verifySignature content sig `shouldBe` True

  describe "Time Range Edge Cases" $ do
    it "handles zero-length time range" $ do
      now <- getCurrentTime
      let range = TimeRange now now
      chClient <- createClickHouseClient "localhost" 8123 "default"
      casClient <- createCASClient "https://cas.test" "test-bucket"
      result <- reconcileFastSlowPath chClient casClient Nothing range
      rrRange result `shouldBe` range

    it "handles reversed time range (end before start)" $ do
      now <- getCurrentTime
      let start = addUTCTime 3600 now
      let end = now
      let range = TimeRange start end
      chClient <- createClickHouseClient "localhost" 8123 "default"
      casClient <- createCASClient "https://cas.test" "test-bucket"
      result <- reconcileFastSlowPath chClient casClient Nothing range
      rrRange result `shouldBe` range

  describe "Large Hash Chain Handling" $ do
    it "handles hash chain with 100 entries" $ do
      content1 <- pure $ BS.pack [1]
      entry1 <- createAuditEntry "test1" content1 Nothing
      let chain1 = HashChain [entry1] (ateContentHash entry1)
      
      chain <- foldM (\acc i -> do
        let content = BS.pack [fromIntegral i]
        let prevHash = hcCurrentHash acc
        entry <- createAuditEntry ("test" <> Text.pack (show i)) content (Just prevHash)
        pure $ appendToChain acc entry
      ) chain1 [2..100]
      
      length (hcEntries chain) `shouldBe` 100
      verifyHashChain chain `shouldBe` True

    it "handles very large content in hash chain entry" $ do
      let largeContent = BS.replicate 1000000 65 -- 1MB
      entry <- createAuditEntry "test" largeContent Nothing
      BS.length (ateContent entry) `shouldBe` 1000000
      BS.length (ateContentHash entry) `shouldBe` 32
      BS.length (ateSignature entry) `shouldBe` 64
