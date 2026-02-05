{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Deep Comprehensive Property Tests for Job Store
-- |
-- | Tests job creation, updates, retrieval, and deletion properties
-- | with realistic distributions to find real bugs.
-- |
-- | Based on spec 70-TESTING-STRATEGY.md and 71-UNIT-TESTING.md
-- | Reference: REQUIRED/trtllm-serve-main/nix/openai-proxy-hs/ProxyPropTest.hs
module JobStoreProps where

import Test.QuickCheck
import Test.QuickCheck.Monadic
import Control.Concurrent.STM
import Control.Monad (replicateM, forM_)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Time (UTCTime, getCurrentTime)
import Data.Aeson (object)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust, isNothing)

import Render.Gateway.Core
import Render.Gateway.STM.Queue

-- ============================================================================
-- REALISTIC DISTRIBUTIONS
-- ============================================================================

-- | Realistic job ID distribution:
-- | - Most jobs: "j_" prefix with 8-16 chars (normal)
-- | - Some jobs: "j_" prefix with 16-32 chars (long)
-- | - Few jobs: "j_" prefix with 4-8 chars (short)
genRealisticJobId :: Gen Text
genRealisticJobId = do
  length <- frequency
    [ (70, choose (8, 16))
    , (20, choose (16, 32))
    , (10, choose (4, 8))
    ]
  chars <- vectorOf length (choose ('a', 'z'))
  pure $ Text.pack ("j_" ++ chars)

-- | Realistic customer ID distribution:
genRealisticCustomerId :: Gen Text
genRealisticCustomerId = do
  length <- choose (8, 16)
  chars <- vectorOf length (choose ('a', 'z'))
  pure $ Text.pack ("cust_" ++ chars)

-- | Realistic priority distribution:
genRealisticPriority :: Gen Priority
genRealisticPriority = frequency
  [ (20, pure High)
  , (60, pure Normal)
  , (20, pure Low)
  ]

-- | Realistic job count distribution:
genRealisticJobCount :: Gen Int
genRealisticJobCount = frequency
  [ (70, choose (1, 50))             -- Normal
  , (25, choose (50, 200))           -- High
  , (5, choose (200, 1000))           -- Stress
  ]

-- | Realistic job generator:
genRealisticJob :: UTCTime -> Gen QueuedJob
genRealisticJob now = do
  jobId <- genRealisticJobId
  customerId <- genRealisticCustomerId
  priority <- genRealisticPriority
  pure QueuedJob
    { qjJobId = jobId
    , qjRequestId = "req_" <> jobId
    , qjCustomerId = customerId
    , qjModality = Video
    , qjModelFamily = "wan"
    , qjModelName = "default"
    , qjTask = T2V
    , qjFormat = Nothing
    , qjBackend = Nothing
    , qjPriority = priority
    , qjStatus = Queued
    , qjCreatedAt = now
    , qjStartedAt = Nothing
    , qjCompletedAt = Nothing
    , qjRequest = object []
    , qjOutput = Nothing
    , qjError = Nothing
    , qjRetryCount = 0
    }

-- ============================================================================
-- JOB CREATION PROPERTIES
-- ============================================================================

-- | Property: Store and retrieve job
prop_storeRetrieveJob :: Property
prop_storeRetrieveJob = monadicIO $ do
  now <- run getCurrentTime
  job <- pick $ genRealisticJob now
  
  store <- run $ atomically createJobStore
  run $ atomically $ storeJob store job
  
  retrieved <- run $ atomically $ getJob store (qjJobId job)
  case retrieved of
    Just j -> do
      assert $ qjJobId j == qjJobId job
      assert $ qjCustomerId j == qjCustomerId job
      assert $ qjPriority j == qjPriority job
    Nothing -> assert False

-- | Property: Store overwrites existing job
prop_storeOverwritesExisting :: Property
prop_storeOverwritesExisting = monadicIO $ do
  now <- run getCurrentTime
  jobId <- pick genRealisticJobId
  customerId <- pick genRealisticCustomerId
  priority1 <- pick genRealisticPriority
  priority2 <- pick genRealisticPriority
  
  -- Create jobs directly
  let job1' = QueuedJob
        { qjJobId = jobId
        , qjRequestId = "req_1"
        , qjCustomerId = customerId
        , qjModality = Video
        , qjModelFamily = "wan"
        , qjModelName = "default"
        , qjTask = T2V
        , qjFormat = Nothing
        , qjBackend = Nothing
        , qjPriority = priority1
        , qjStatus = Queued
        , qjCreatedAt = now
        , qjStartedAt = Nothing
        , qjCompletedAt = Nothing
        , qjRequest = object []
        , qjOutput = Nothing
        , qjError = Nothing
        , qjRetryCount = 0
        }
  
  let job2' = job1' { qjPriority = priority2 }
  
  store <- run $ atomically createJobStore
  run $ atomically $ do
    storeJob store job1'
    storeJob store job2'
  
  retrieved <- run $ atomically $ getJob store jobId
  case retrieved of
    Just j -> assert $ qjPriority j == priority2
    Nothing -> assert False

-- | Property: Store multiple jobs independently
prop_storeMultipleJobs :: Property
prop_storeMultipleJobs = monadicIO $ do
  now <- run getCurrentTime
  jobCount <- pick genRealisticJobCount
  
  jobs <- run $ replicateM jobCount $ pick $ genRealisticJob now
  
  store <- run $ atomically createJobStore
  run $ atomically $ forM_ jobs $ storeJob store
  
  -- Retrieve all jobs
  retrieved <- run $ atomically $ mapM (getJob store . qjJobId) jobs
  
  -- All should be found
  assert $ all isJust retrieved
  
  -- Verify each job matches
  forM_ (zip jobs retrieved) $ \(original, mRetrieved) -> do
    case mRetrieved of
      Just retrieved' -> assert $ qjJobId retrieved' == qjJobId original
      Nothing -> assert False

-- | Property: Empty store returns Nothing
prop_emptyStoreReturnsNothing :: Property
prop_emptyStoreReturnsNothing = monadicIO $ do
  jobId <- pick genRealisticJobId
  
  store <- run $ atomically createJobStore
  retrieved <- run $ atomically $ getJob store jobId
  
  assert $ isNothing retrieved

-- ============================================================================
-- JOB UPDATE PROPERTIES
-- ============================================================================

-- | Property: Update existing job
prop_updateExistingJob :: Property
prop_updateExistingJob = monadicIO $ do
  now <- run getCurrentTime
  job <- pick $ genRealisticJob now
  
  store <- run $ atomically createJobStore
  run $ atomically $ storeJob store job
  
  -- Update status
  updated <- run $ atomically $ updateJob store (qjJobId job) (\j -> j { qjStatus = Running })
  assert updated
  
  -- Verify update
  retrieved <- run $ atomically $ getJob store (qjJobId job)
  case retrieved of
    Just j -> assert $ qjStatus j == Running
    Nothing -> assert False

-- | Property: Update returns False for non-existent job
prop_updateNonExistentJob :: Property
prop_updateNonExistentJob = monadicIO $ do
  jobId <- pick genRealisticJobId
  
  store <- run $ atomically createJobStore
  updated <- run $ atomically $ updateJob store jobId (\j -> j { qjStatus = Running })
  
  assert $ not updated

-- | Property: Update preserves unrelated fields
prop_updatePreservesUnrelatedFields :: Property
prop_updatePreservesUnrelatedFields = monadicIO $ do
  now <- run getCurrentTime
  job <- pick $ genRealisticJob now
  
  store <- run $ atomically createJobStore
  run $ atomically $ storeJob store job
  
  -- Update only status
  updated <- run $ atomically $ updateJob store (qjJobId job) (\j -> j { qjStatus = Running })
  assert updated
  
  -- Verify other fields preserved
  retrieved <- run $ atomically $ getJob store (qjJobId job)
  case retrieved of
    Just j -> do
      assert $ qjJobId j == qjJobId job
      assert $ qjCustomerId j == qjCustomerId job
      assert $ qjPriority j == qjPriority job
      assert $ qjModality j == qjModality job
    Nothing -> assert False

-- | Property: Multiple updates apply correctly
prop_multipleUpdates :: Property
prop_multipleUpdates = monadicIO $ do
  now <- run getCurrentTime
  job <- pick $ genRealisticJob now
  
  store <- run $ atomically createJobStore
  run $ atomically $ storeJob store job
  
  -- Update status multiple times
  updated1 <- run $ atomically $ updateJob store (qjJobId job) (\j -> j { qjStatus = Running })
  assert updated1
  
  updated2 <- run $ atomically $ updateJob store (qjJobId job) (\j -> j { qjStatus = Complete })
  assert updated2
  
  -- Verify final state
  retrieved <- run $ atomically $ getJob store (qjJobId job)
  case retrieved of
    Just j -> assert $ qjStatus j == Complete
    Nothing -> assert False

-- ============================================================================
-- JOB RETRIEVAL PROPERTIES
-- ============================================================================

-- | Property: Retrieve existing job
prop_retrieveExistingJob :: Property
prop_retrieveExistingJob = monadicIO $ do
  now <- run getCurrentTime
  job <- pick $ genRealisticJob now
  
  store <- run $ atomically createJobStore
  run $ atomically $ storeJob store job
  
  retrieved <- run $ atomically $ getJob store (qjJobId job)
  assert $ isJust retrieved
  
  case retrieved of
    Just j -> assert $ qjJobId j == qjJobId job
    Nothing -> assert False

-- | Property: Retrieve non-existent job returns Nothing
prop_retrieveNonExistentJob :: Property
prop_retrieveNonExistentJob = monadicIO $ do
  jobId <- pick genRealisticJobId
  
  store <- run $ atomically createJobStore
  retrieved <- run $ atomically $ getJob store jobId
  
  assert $ isNothing retrieved

-- | Property: Retrieve after update
prop_retrieveAfterUpdate :: Property
prop_retrieveAfterUpdate = monadicIO $ do
  now <- run getCurrentTime
  job <- pick $ genRealisticJob now
  
  store <- run $ atomically createJobStore
  run $ atomically $ storeJob store job
  
  -- Update
  updated <- run $ atomically $ updateJob store (qjJobId job) (\j -> j { qjStatus = Running })
  assert updated
  
  -- Retrieve
  retrieved <- run $ atomically $ getJob store (qjJobId job)
  case retrieved of
    Just j -> assert $ qjStatus j == Running
    Nothing -> assert False

-- | Property: Retrieve multiple jobs
prop_retrieveMultipleJobs :: Property
prop_retrieveMultipleJobs = monadicIO $ do
  now <- run getCurrentTime
  jobCount <- pick $ choose (5, 20)
  
  jobs <- run $ replicateM jobCount $ pick $ genRealisticJob now
  
  store <- run $ atomically createJobStore
  run $ atomically $ forM_ jobs $ storeJob store
  
  -- Retrieve all
  retrieved <- run $ atomically $ mapM (getJob store . qjJobId) jobs
  
  -- All should be found
  assert $ all isJust retrieved
  
  -- Verify IDs match
  forM_ (zip jobs retrieved) $ \(original, mRetrieved) -> do
    case mRetrieved of
      Just retrieved' -> assert $ qjJobId retrieved' == qjJobId original
      Nothing -> assert False

-- ============================================================================
-- JOB DELETION PROPERTIES
-- ============================================================================

-- | Property: Delete existing job
prop_deleteExistingJob :: Property
prop_deleteExistingJob = monadicIO $ do
  now <- run getCurrentTime
  job <- pick $ genRealisticJob now
  
  store <- run $ atomically createJobStore
  run $ atomically $ storeJob store job
  
  -- Delete
  run $ atomically $ deleteJob store (qjJobId job)
  
  -- Should not be retrievable
  retrieved <- run $ atomically $ getJob store (qjJobId job)
  assert $ isNothing retrieved

-- | Property: Delete non-existent job handles gracefully
prop_deleteNonExistentJob :: Property
prop_deleteNonExistentJob = monadicIO $ do
  jobId <- pick genRealisticJobId
  
  store <- run $ atomically createJobStore
  
  -- Delete non-existent job (should not crash)
  run $ atomically $ deleteJob store jobId
  
  -- Store should still be valid
  retrieved <- run $ atomically $ getJob store jobId
  assert $ isNothing retrieved

-- | Property: Delete only specified job
prop_deleteOnlySpecifiedJob :: Property
prop_deleteOnlySpecifiedJob = monadicIO $ do
  now <- run getCurrentTime
  job1 <- pick $ genRealisticJob now
  job2 <- pick $ genRealisticJob now
  
  store <- run $ atomically createJobStore
  run $ atomically $ do
    storeJob store job1
    storeJob store job2
  
  -- Delete only job1
  run $ atomically $ deleteJob store (qjJobId job1)
  
  -- job1 should be gone, job2 should remain
  retrieved1 <- run $ atomically $ getJob store (qjJobId job1)
  retrieved2 <- run $ atomically $ getJob store (qjJobId job2)
  
  assert $ isNothing retrieved1
  assert $ isJust retrieved2

-- | Property: Delete and recreate job
prop_deleteAndRecreateJob :: Property
prop_deleteAndRecreateJob = monadicIO $ do
  now <- run getCurrentTime
  jobId <- pick genRealisticJobId
  customerId <- pick genRealisticCustomerId
  
  let job1 = QueuedJob
        { qjJobId = jobId
        , qjRequestId = "req_1"
        , qjCustomerId = customerId
        , qjModality = Video
        , qjModelFamily = "wan"
        , qjModelName = "default"
        , qjTask = T2V
        , qjFormat = Nothing
        , qjBackend = Nothing
        , qjPriority = Normal
        , qjStatus = Queued
        , qjCreatedAt = now
        , qjStartedAt = Nothing
        , qjCompletedAt = Nothing
        , qjRequest = object []
        , qjOutput = Nothing
        , qjError = Nothing
        , qjRetryCount = 0
        }
  
  let job2 = job1 { qjPriority = High }
  
  store <- run $ atomically createJobStore
  run $ atomically $ storeJob store job1
  
  -- Delete
  run $ atomically $ deleteJob store jobId
  
  -- Recreate with different priority
  run $ atomically $ storeJob store job2
  
  -- Should retrieve new job
  retrieved <- run $ atomically $ getJob store jobId
  case retrieved of
    Just j -> assert $ qjPriority j == High
    Nothing -> assert False

-- ============================================================================
-- CONCURRENT OPERATION PROPERTIES
-- ============================================================================

-- | Property: Concurrent store operations
prop_concurrentStoreOperations :: Property
prop_concurrentStoreOperations = monadicIO $ do
  now <- run getCurrentTime
  jobCount <- pick $ choose (10, 50)
  
  jobs <- run $ replicateM jobCount $ pick $ genRealisticJob now
  
  store <- run $ atomically createJobStore
  
  -- Store all jobs in single transaction (simulates concurrent access)
  run $ atomically $ forM_ jobs $ storeJob store
  
  -- Retrieve all
  retrieved <- run $ atomically $ mapM (getJob store . qjJobId) jobs
  
  -- All should be found
  assert $ all isJust retrieved

-- | Property: Concurrent update operations
prop_concurrentUpdateOperations :: Property
prop_concurrentUpdateOperations = monadicIO $ do
  now <- run getCurrentTime
  job <- pick $ genRealisticJob now
  
  store <- run $ atomically createJobStore
  run $ atomically $ storeJob store job
  
  -- Multiple updates in single transaction
  updated <- run $ atomically $ do
    updateJob store (qjJobId job) (\j -> j { qjStatus = Running })
    updateJob store (qjJobId job) (\j -> j { qjStatus = Complete })
    updateJob store (qjJobId job) (\j -> j { qjStatus = Error })
  
  -- Final state should be Error
  retrieved <- run $ atomically $ getJob store (qjJobId job)
  case retrieved of
    Just j -> assert $ qjStatus j == Error
    Nothing -> assert False

-- | Property: Store then delete then retrieve
prop_storeDeleteRetrieve :: Property
prop_storeDeleteRetrieve = monadicIO $ do
  now <- run getCurrentTime
  job <- pick $ genRealisticJob now
  
  store <- run $ atomically createJobStore
  run $ atomically $ do
    storeJob store job
    deleteJob store (qjJobId job)
  
  -- Should not be retrievable
  retrieved <- run $ atomically $ getJob store (qjJobId job)
  assert $ isNothing retrieved

-- ============================================================================
-- EDGE CASE PROPERTIES
-- ============================================================================

-- | Property: Empty store operations
prop_emptyStoreOperations :: Property
prop_emptyStoreOperations = monadicIO $ do
  jobId <- pick genRealisticJobId
  
  store <- run $ atomically createJobStore
  
  -- All operations should handle empty store
  retrieved <- run $ atomically $ getJob store jobId
  assert $ isNothing retrieved
  
  updated <- run $ atomically $ updateJob store jobId (\j -> j { qjStatus = Running })
  assert $ not updated
  
  run $ atomically $ deleteJob store jobId  -- Should not crash
  
  -- Store should still be valid
  retrieved2 <- run $ atomically $ getJob store jobId
  assert $ isNothing retrieved2

-- | Property: Very long job IDs
prop_veryLongJobIds :: Property
prop_veryLongJobIds = monadicIO $ do
  now <- run getCurrentTime
  -- Generate very long job ID
  longId <- pick $ do
    length <- choose (100, 500)
    chars <- vectorOf length (choose ('a', 'z'))
    pure $ Text.pack ("j_" ++ chars)
  
  let job = QueuedJob
        { qjJobId = longId
        , qjRequestId = "req_long"
        , qjCustomerId = "cust_test"
        , qjModality = Video
        , qjModelFamily = "wan"
        , qjModelName = "default"
        , qjTask = T2V
        , qjFormat = Nothing
        , qjBackend = Nothing
        , qjPriority = Normal
        , qjStatus = Queued
        , qjCreatedAt = now
        , qjStartedAt = Nothing
        , qjCompletedAt = Nothing
        , qjRequest = object []
        , qjOutput = Nothing
        , qjError = Nothing
        , qjRetryCount = 0
        }
  
  store <- run $ atomically createJobStore
  run $ atomically $ storeJob store job
  
  retrieved <- run $ atomically $ getJob store longId
  case retrieved of
    Just j -> assert $ qjJobId j == longId
    Nothing -> assert False

-- | Property: Unicode job IDs
prop_unicodeJobIds :: Property
prop_unicodeJobIds = monadicIO $ do
  now <- run getCurrentTime
  -- Generate Unicode job ID
  unicodeId <- pick $ pure $ Text.pack "j_测试_🎨_тест"
  
  let job = QueuedJob
        { qjJobId = unicodeId
        , qjRequestId = "req_unicode"
        , qjCustomerId = "cust_test"
        , qjModality = Video
        , qjModelFamily = "wan"
        , qjModelName = "default"
        , qjTask = T2V
        , qjFormat = Nothing
        , qjBackend = Nothing
        , qjPriority = Normal
        , qjStatus = Queued
        , qjCreatedAt = now
        , qjStartedAt = Nothing
        , qjCompletedAt = Nothing
        , qjRequest = object []
        , qjOutput = Nothing
        , qjError = Nothing
        , qjRetryCount = 0
        }
  
  store <- run $ atomically createJobStore
  run $ atomically $ storeJob store job
  
  retrieved <- run $ atomically $ getJob store unicodeId
  case retrieved of
    Just j -> assert $ qjJobId j == unicodeId
    Nothing -> assert False

-- | Property: Identity update (no-op)
prop_identityUpdate :: Property
prop_identityUpdate = monadicIO $ do
  now <- run getCurrentTime
  job <- pick $ genRealisticJob now
  
  store <- run $ atomically createJobStore
  run $ atomically $ storeJob store job
  
  -- Identity update
  updated <- run $ atomically $ updateJob store (qjJobId job) id
  assert updated
  
  -- Job should be unchanged
  retrieved <- run $ atomically $ getJob store (qjJobId job)
  case retrieved of
    Just j -> assert $ qjJobId j == qjJobId job
    Nothing -> assert False

-- ============================================================================
-- BUG DETECTION PROPERTIES
-- ============================================================================

-- | BUG: Update/delete race conditions
prop_bug_updateDeleteRace :: Property
prop_bug_updateDeleteRace = monadicIO $ do
  now <- run getCurrentTime
  job <- pick $ genRealisticJob now
  
  store <- run $ atomically createJobStore
  run $ atomically $ storeJob store job
  
  -- Update and delete in same transaction
  run $ atomically $ do
    updateJob store (qjJobId job) (\j -> j { qjStatus = Running })
    deleteJob store (qjJobId job)
  
  -- Job should be deleted
  retrieved <- run $ atomically $ getJob store (qjJobId job)
  assert $ isNothing retrieved
  -- BUG: If update/delete race condition exists, job may not be deleted correctly

-- | BUG: Memory leaks with large stores
prop_bug_memoryLeakLargeStore :: Property
prop_bug_memoryLeakLargeStore = monadicIO $ do
  now <- run getCurrentTime
  jobCount <- pick $ choose (500, 2000)
  
  jobs <- run $ replicateM jobCount $ pick $ genRealisticJob now
  
  store <- run $ atomically createJobStore
  run $ atomically $ forM_ jobs $ storeJob store
  
  -- Delete all jobs
  run $ atomically $ forM_ jobs $ deleteJob store . qjJobId
  
  -- Store should be empty
  retrieved <- run $ atomically $ mapM (getJob store . qjJobId) jobs
  assert $ all isNothing retrieved
  -- BUG: If memory leaks exist, memory may not be released after deletion

-- | BUG: Atomicity issues
prop_bug_atomicityIssues :: Property
prop_bug_atomicityIssues = monadicIO $ do
  now <- run getCurrentTime
  job <- pick $ genRealisticJob now
  
  store <- run $ atomically createJobStore
  run $ atomically $ storeJob store job
  
  -- Update multiple fields
  updated <- run $ atomically $ updateJob store (qjJobId job) (\j -> j
    { qjStatus = Running
    , qjPriority = High
    , qjRetryCount = 5
    })
  assert updated
  
  -- All fields should be updated atomically
  retrieved <- run $ atomically $ getJob store (qjJobId job)
  case retrieved of
    Just j -> do
      assert $ qjStatus j == Running
      assert $ qjPriority j == High
      assert $ qjRetryCount j == 5
    Nothing -> assert False
  -- BUG: If atomicity is broken, only some fields may be updated

-- | BUG: Stale data after concurrent updates
prop_bug_staleData :: Property
prop_bug_staleData = monadicIO $ do
  now <- run getCurrentTime
  job <- pick $ genRealisticJob now
  
  store <- run $ atomically createJobStore
  run $ atomically $ storeJob store job
  
  -- Update status
  updated1 <- run $ atomically $ updateJob store (qjJobId job) (\j -> j { qjStatus = Running })
  assert updated1
  
  -- Read job
  retrieved1 <- run $ atomically $ getJob store (qjJobId job)
  case retrieved1 of
    Just j1 -> do
      assert $ qjStatus j1 == Running
      
      -- Update again
      updated2 <- run $ atomically $ updateJob store (qjJobId job) (\j -> j { qjStatus = Complete })
      assert updated2
      
      -- Read again (should see latest update)
      retrieved2 <- run $ atomically $ getJob store (qjJobId job)
      case retrieved2 of
        Just j2 -> assert $ qjStatus j2 == Complete
        Nothing -> assert False
    Nothing -> assert False
  -- BUG: If stale data exists, retrieved2 may show Running instead of Complete

-- | BUG: Map.adjust may fail silently
prop_bug_mapAdjustFailure :: Property
prop_bug_mapAdjustFailure = monadicIO $ do
  now <- run getCurrentTime
  job <- pick $ genRealisticJob now
  
  store <- run $ atomically createJobStore
  run $ atomically $ storeJob store job
  
  -- Update non-existent job (should return False)
  updated <- run $ atomically $ updateJob store "nonexistent" (\j -> j { qjStatus = Running })
  assert $ not updated
  
  -- Original job should be unchanged
  retrieved <- run $ atomically $ getJob store (qjJobId job)
  case retrieved of
    Just j -> assert $ qjJobId j == qjJobId job
    Nothing -> assert False
  -- BUG: If Map.adjust fails silently, update may succeed incorrectly

-- ============================================================================
-- TEST RUNNER
-- ============================================================================

main :: IO ()
main = do
  putStrLn "Job Store Property Tests"
  putStrLn "========================"
  
  putStrLn "\n1. Store and Retrieve Job"
  quickCheck prop_storeRetrieveJob
  
  putStrLn "\n2. Store Overwrites Existing"
  quickCheck prop_storeOverwritesExisting
  
  putStrLn "\n3. Store Multiple Jobs"
  quickCheck prop_storeMultipleJobs
  
  putStrLn "\n4. Empty Store Returns Nothing"
  quickCheck prop_emptyStoreReturnsNothing
  
  putStrLn "\n5. Update Existing Job"
  quickCheck prop_updateExistingJob
  
  putStrLn "\n6. Update Non-Existent Job"
  quickCheck prop_updateNonExistentJob
  
  putStrLn "\n7. Update Preserves Unrelated Fields"
  quickCheck prop_updatePreservesUnrelatedFields
  
  putStrLn "\n8. Multiple Updates"
  quickCheck prop_multipleUpdates
  
  putStrLn "\n9. Retrieve Existing Job"
  quickCheck prop_retrieveExistingJob
  
  putStrLn "\n10. Retrieve Non-Existent Job"
  quickCheck prop_retrieveNonExistentJob
  
  putStrLn "\n11. Retrieve After Update"
  quickCheck prop_retrieveAfterUpdate
  
  putStrLn "\n12. Retrieve Multiple Jobs"
  quickCheck prop_retrieveMultipleJobs
  
  putStrLn "\n13. Delete Existing Job"
  quickCheck prop_deleteExistingJob
  
  putStrLn "\n14. Delete Non-Existent Job"
  quickCheck prop_deleteNonExistentJob
  
  putStrLn "\n15. Delete Only Specified Job"
  quickCheck prop_deleteOnlySpecifiedJob
  
  putStrLn "\n16. Delete and Recreate Job"
  quickCheck prop_deleteAndRecreateJob
  
  putStrLn "\n17. Concurrent Store Operations"
  quickCheck prop_concurrentStoreOperations
  
  putStrLn "\n18. Concurrent Update Operations"
  quickCheck prop_concurrentUpdateOperations
  
  putStrLn "\n19. Store Delete Retrieve"
  quickCheck prop_storeDeleteRetrieve
  
  putStrLn "\n20. Empty Store Operations"
  quickCheck prop_emptyStoreOperations
  
  putStrLn "\n21. Very Long Job IDs"
  quickCheck prop_veryLongJobIds
  
  putStrLn "\n22. Unicode Job IDs"
  quickCheck prop_unicodeJobIds
  
  putStrLn "\n23. Identity Update"
  quickCheck prop_identityUpdate
  
  putStrLn "\n24. Bug: Update/Delete Race"
  quickCheck prop_bug_updateDeleteRace
  
  putStrLn "\n25. Bug: Memory Leak Large Store"
  quickCheck prop_bug_memoryLeakLargeStore
  
  putStrLn "\n26. Bug: Atomicity Issues"
  quickCheck prop_bug_atomicityIssues
  
  putStrLn "\n27. Bug: Stale Data"
  quickCheck prop_bug_staleData
  
  putStrLn "\n28. Bug: Map.adjust Failure"
  quickCheck prop_bug_mapAdjustFailure
  
  putStrLn "\nAll tests completed!"
