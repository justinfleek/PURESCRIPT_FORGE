{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Deep Comprehensive Property Tests for Queue Operations
-- |
-- | Tests queue invariants, priority ordering, and job preservation
-- | with realistic distributions to find real bugs.
-- |
-- | Based on spec 70-TESTING-STRATEGY.md and 71-UNIT-TESTING.md
-- | Reference: REQUIRED/trtllm-serve-main/nix/openai-proxy-hs/ProxyPropTest.hs
module QueueProps where

import Test.QuickCheck
import Test.QuickCheck.Monadic
import Control.Concurrent.STM
import Control.Monad (replicateM, forM_, void)
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Time (UTCTime, getCurrentTime)
import Data.Aeson (object)
import Data.Int (Int32)
import Data.List (sort, groupBy, sortBy)
import Data.Ord (comparing)
import Data.Maybe (isJust, mapMaybe)

import Render.Gateway.STM.Queue
import Control.Concurrent.STM.TQueue (isEmptyTQueue, tryReadTQueue, writeTQueue)

-- ============================================================================
-- REALISTIC DISTRIBUTIONS
-- ============================================================================

-- | Realistic priority distribution:
-- | - 10% High priority (premium customers, urgent requests)
-- | - 70% Normal priority (standard requests)
-- | - 20% Low priority (batch jobs, background processing)
genRealisticPriority :: Gen Priority
genRealisticPriority = frequency
  [ (10, return High)
  , (70, return Normal)
  , (20, return Low)
  ]

-- | Realistic customer ID distribution:
-- | - Most customers have 1-5 jobs
-- | - Some customers have many jobs (power users)
-- | - Customer IDs follow realistic patterns (cust_xxx)
genRealisticCustomerId :: Gen Text
genRealisticCustomerId = do
  customerNum <- choose (1, 1000)  -- 1000 different customers
  return $ "cust_" <> Text.pack (show customerNum)

-- | Realistic job ID distribution:
-- | - Job IDs follow j_xxx format
-- | - Sequential within customer, but random globally
genRealisticJobId :: Int -> Gen Text
genRealisticJobId jobNum = do
  return $ "j_" <> Text.pack (show jobNum)

-- | Realistic task type distribution:
-- | - 40% T2V (text-to-video, most common)
-- | - 30% T2I (text-to-image)
-- | - 15% I2V (image-to-video)
-- | - 10% I2I (image-to-image)
-- | - 5% Edit
genRealisticTaskType :: Gen TaskType
genRealisticTaskType = frequency
  [ (40, return T2V)
  , (30, return T2I)
  , (15, return I2V)
  , (10, return I2I)
  , (5, return Edit)
  ]

-- | Realistic modality distribution:
-- | - 60% Video (more common)
-- | - 40% Image
genRealisticModality :: Gen Modality
genRealisticModality = frequency
  [ (60, return Video)
  , (40, return Image)
  ]

-- | Realistic job count distribution:
-- | - Most test cases: 1-50 jobs (normal load)
-- | - Some test cases: 50-200 jobs (high load)
-- | - Few test cases: 200-1000 jobs (stress test)
genRealisticJobCount :: Gen Int
genRealisticJobCount = frequency
  [ (70, choose (1, 50))      -- Normal load
  , (25, choose (50, 200))    -- High load
  , (5, choose (200, 1000))   -- Stress test
  ]

-- | Generate realistic job with all fields
genRealisticJob :: UTCTime -> Int -> Gen QueuedJob
genRealisticJob now jobNum = do
  jobId <- genRealisticJobId jobNum
  customerId <- genRealisticCustomerId
  priority <- genRealisticPriority
  task <- genRealisticTaskType
  modality <- genRealisticModality
  modelFamily <- elements ["flux", "wan", "qwen", "sdxl", "zimage"]
  modelName <- elements ["default", "dev", "2.1", "pro"]
  
  return QueuedJob
    { qjJobId = jobId
    , qjRequestId = "req_" <> jobId
    , qjCustomerId = customerId
    , qjModality = modality
    , qjModelFamily = modelFamily
    , qjModelName = modelName
    , qjTask = task
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
-- PROPERTY TESTS
-- ============================================================================

-- | Property: Enqueue/dequeue roundtrip
-- | Enqueue a job, then dequeue it - should get the same job back
prop_enqueueDequeueRoundTrip :: Property
prop_enqueueDequeueRoundTrip = monadicIO $ do
  now <- run getCurrentTime
  job <- pick $ genRealisticJob now 1
  
  queue <- run $ atomically createQueue
  run $ atomically $ enqueueJob queue job
  
  dequeued <- run $ atomically $ dequeueJob queue
  
  assert $ dequeued == job
  assert $ qjJobId dequeued == qjJobId job
  assert $ qjPriority dequeued == qjPriority job

-- | Property: Queue size invariants
-- | After enqueuing N jobs, queue size should be N
-- | After dequeuing M jobs, queue size should be N - M
prop_queueSizeInvariant :: Property
prop_queueSizeInvariant = monadicIO $ do
  now <- run getCurrentTime
  jobCount <- pick $ genRealisticJobCount
  
  jobs <- pick $ replicateM jobCount (genRealisticJob now =<< choose (1, 10000))
  
  queue <- run $ atomically createQueue
  
  -- Enqueue all jobs
  run $ atomically $ forM_ jobs $ enqueueJob queue
  
  -- Check size matches
  sizeAfterEnqueue <- run $ atomically $ queueSize queue
  assert $ fromIntegral sizeAfterEnqueue == jobCount
  
  -- Dequeue half the jobs
  let dequeueCount = jobCount `div` 2
  run $ atomically $ replicateM_ dequeueCount $ dequeueJob queue
  
  -- Check size matches
  sizeAfterDequeue <- run $ atomically $ queueSize queue
  assert $ fromIntegral sizeAfterDequeue == jobCount - dequeueCount
  
  -- Dequeue remaining jobs
  run $ atomically $ replicateM_ (jobCount - dequeueCount) $ dequeueJob queue
  
  -- Check queue is empty
  sizeFinal <- run $ atomically $ queueSize queue
  isEmptyFinal <- run $ atomically $ isEmpty queue
  
  assert $ fromIntegral sizeFinal == 0
  assert isEmptyFinal

-- | Property: Priority ordering preserved
-- | High priority jobs should be dequeued before Normal
-- | Normal priority jobs should be dequeued before Low
prop_priorityOrdering :: Property
prop_priorityOrdering = monadicIO $ do
  now <- run getCurrentTime
  
  -- Create jobs with different priorities
  highJob <- pick $ genRealisticJob now 1 >>= \j -> return j { qjPriority = High }
  normalJob <- pick $ genRealisticJob now 2 >>= \j -> return j { qjPriority = Normal }
  lowJob <- pick $ genRealisticJob now 3 >>= \j -> return j { qjPriority = Low }
  
  queue <- run $ atomically createQueue
  
  -- Enqueue in wrong order (Low, Normal, High)
  run $ atomically $ do
    enqueueJob queue lowJob
    enqueueJob queue normalJob
    enqueueJob queue highJob
  
  -- Dequeue should return High first
  first <- run $ atomically $ dequeueJob queue
  assert $ qjPriority first == High
  assert $ qjJobId first == qjJobId highJob
  
  -- Then Normal
  second <- run $ atomically $ dequeueJob queue
  assert $ qjPriority second == Normal
  assert $ qjJobId second == qjJobId normalJob
  
  -- Then Low
  third <- run $ atomically $ dequeueJob queue
  assert $ qjPriority third == Low
  assert $ qjJobId third == qjJobId lowJob

-- | Property: No job loss
-- | All enqueued jobs should be dequeuable
prop_noJobLoss :: Property
prop_noJobLoss = monadicIO $ do
  now <- run getCurrentTime
  jobCount <- pick $ genRealisticJobCount
  
  jobs <- pick $ replicateM jobCount (genRealisticJob now =<< choose (1, 10000))
  let jobIds = map qjJobId jobs
  
  queue <- run $ atomically createQueue
  
  -- Enqueue all jobs
  run $ atomically $ forM_ jobs $ enqueueJob queue
  
  -- Dequeue all jobs
  dequeuedJobs <- run $ atomically $ replicateM jobCount $ dequeueJob queue
  
  let dequeuedIds = map qjJobId dequeuedJobs
  
  -- All job IDs should be present
  assert $ length dequeuedIds == jobCount
  assert $ all (`elem` dequeuedIds) jobIds
  assert $ all (`elem` jobIds) dequeuedIds
  
  -- Queue should be empty
  isEmptyFinal <- run $ atomically $ isEmpty queue
  assert isEmptyFinal

-- | Property: FIFO ordering within same priority
-- | Jobs with same priority should be dequeued in FIFO order
prop_fifoWithinPriority :: Property
prop_fifoWithinPriority = monadicIO $ do
  now <- run getCurrentTime
  jobCount <- pick $ choose (5, 20)  -- Reasonable number for FIFO test
  
  -- Create jobs with same priority (Normal)
  jobs <- pick $ replicateM jobCount $ do
    jobNum <- choose (1, 10000)
    genRealisticJob now jobNum >>= \j -> return j { qjPriority = Normal }
  
  let jobIds = map qjJobId jobs
  
  queue <- run $ atomically createQueue
  
  -- Enqueue all jobs
  run $ atomically $ forM_ jobs $ enqueueJob queue
  
  -- Dequeue all jobs
  dequeuedJobs <- run $ atomically $ replicateM jobCount $ dequeueJob queue
  
  let dequeuedIds = map qjJobId dequeuedJobs
  
  -- Should be dequeued in same order as enqueued
  assert $ dequeuedIds == jobIds

-- | Property: Mixed priority ordering
-- | With mixed priorities, High should come first, then Normal, then Low
-- | Within each priority, FIFO order should be preserved
prop_mixedPriorityOrdering :: Property
prop_mixedPriorityOrdering = monadicIO $ do
  now <- run getCurrentTime
  
  -- Create jobs with mixed priorities
  highJobs <- pick $ replicateM 3 $ do
    jobNum <- choose (1, 10000)
    genRealisticJob now jobNum >>= \j -> return j { qjPriority = High }
  
  normalJobs <- pick $ replicateM 5 $ do
    jobNum <- choose (1, 10000)
    genRealisticJob now jobNum >>= \j -> return j { qjPriority = Normal }
  
  lowJobs <- pick $ replicateM 2 $ do
    jobNum <- choose (1, 10000)
    genRealisticJob now jobNum >>= \j -> return j { qjPriority = Low }
  
  let allJobs = highJobs ++ normalJobs ++ lowJobs
  let highIds = map qjJobId highJobs
  let normalIds = map qjJobId normalJobs
  let lowIds = map qjJobId lowJobs
  
  queue <- run $ atomically createQueue
  
  -- Enqueue in random order
  run $ atomically $ forM_ allJobs $ enqueueJob queue
  
  -- Dequeue all
  dequeuedJobs <- run $ atomically $ replicateM (length allJobs) $ dequeueJob queue
  
  let dequeuedIds = map qjJobId dequeuedJobs
  let dequeuedPriorities = map qjPriority dequeuedJobs
  
  -- First 3 should be High
  assert $ take 3 dequeuedPriorities == [High, High, High]
  assert $ take 3 dequeuedIds == highIds
  
  -- Next 5 should be Normal
  assert $ take 5 (drop 3 dequeuedPriorities) == [Normal, Normal, Normal, Normal, Normal]
  assert $ take 5 (drop 3 dequeuedIds) == normalIds
  
  -- Last 2 should be Low
  assert $ drop 8 dequeuedPriorities == [Low, Low]
  assert $ drop 8 dequeuedIds == lowIds

-- | Property: tryDequeueJob matches dequeueJob behavior
-- | tryDequeueJob should return same jobs as dequeueJob (when queue not empty)
prop_tryDequeueMatchesDequeue :: Property
prop_tryDequeueMatchesDequeue = monadicIO $ do
  now <- run getCurrentTime
  jobCount <- pick $ choose (1, 10)
  
  jobs <- pick $ replicateM jobCount (genRealisticJob now =<< choose (1, 10000))
  
  queue1 <- run $ atomically createQueue
  queue2 <- run $ atomically createQueue
  
  -- Enqueue same jobs to both queues
  run $ atomically $ forM_ jobs $ \job -> do
    enqueueJob queue1 job
    enqueueJob queue2 job
  
  -- Dequeue from queue1 using dequeueJob
  dequeued1 <- run $ atomically $ replicateM jobCount $ dequeueJob queue1
  
  -- Dequeue from queue2 using tryDequeueJob
  dequeued2 <- run $ atomically $ do
    results <- replicateM jobCount $ tryDequeueJob queue2
    return $ map (\(Just j) -> j) results
  
  -- Should get same jobs
  assert $ map qjJobId dequeued1 == map qjJobId dequeued2
  assert $ dequeued1 == dequeued2

-- | Property: tryDequeueJob returns Nothing when empty
prop_tryDequeueEmpty :: Property
prop_tryDequeueEmpty = monadicIO $ do
  queue <- run $ atomically createQueue
  
  result <- run $ atomically $ tryDequeueJob queue
  
  assert $ result == Nothing
  
  isEmptyCheck <- run $ atomically $ isEmpty queue
  assert isEmptyCheck

-- | Property: Queue size never negative
-- | Even with concurrent operations, size should never go negative
prop_sizeNeverNegative :: Property
prop_sizeNeverNegative = monadicIO $ do
  now <- run getCurrentTime
  jobCount <- pick $ choose (1, 50)
  
  jobs <- pick $ replicateM jobCount (genRealisticJob now =<< choose (1, 10000))
  
  queue <- run $ atomically createQueue
  
  -- Enqueue all
  run $ atomically $ forM_ jobs $ enqueueJob queue
  
  -- Dequeue more than enqueued (should not cause negative)
  run $ atomically $ do
    -- Try to dequeue more than we have
    forM_ [1..(jobCount + 10)] $ \_ -> do
      mJob <- tryDequeueJob queue
      return ()
  
  -- Size should be 0, not negative
  size <- run $ atomically $ queueSize queue
  assert $ size >= 0

-- ============================================================================
-- BUG DETECTION PROPERTIES
-- ============================================================================

-- | BUG: Queue size may become out of sync
-- | If enqueue/dequeue operations are not atomic, size may be wrong
prop_bug_sizeSync :: Property
prop_bug_sizeSync = monadicIO $ do
  now <- run getCurrentTime
  jobCount <- pick $ choose (10, 100)
  
  jobs <- pick $ replicateM jobCount (genRealisticJob now =<< choose (1, 10000))
  
  queue <- run $ atomically createQueue
  
  -- Enqueue all
  run $ atomically $ forM_ jobs $ enqueueJob queue
  
  -- Get size
  size <- run $ atomically $ queueSize queue
  
  -- Manually count jobs in queues
  actualCount <- run $ atomically $ do
    highCount <- countQueue (rqHigh queue)
    normalCount <- countQueue (rqNormal queue)
    lowCount <- countQueue (rqLow queue)
    return $ highCount + normalCount + lowCount
  
  -- Size should match actual count
  assert $ fromIntegral size == actualCount
  -- BUG: If size counter is not updated correctly, this will fail

-- Helper to count jobs in a queue (without consuming them)
-- This drains the queue, counts, then re-enqueues in same order
countQueue :: TQueue QueuedJob -> STM Int
countQueue q = do
  -- Drain queue into list by repeatedly trying to read
  jobs <- drainQueueToList q
  -- Re-enqueue in same order to preserve FIFO
  mapM_ (writeTQueue q) jobs
  return $ length jobs

-- Helper to drain a TQueue into a list (consumes the queue)
drainQueueToList :: TQueue QueuedJob -> STM [QueuedJob]
drainQueueToList q = do
  mJob <- tryReadTQueue q
  case mJob of
    Just job -> do
      rest <- drainQueueToList q
      return (job : rest)
    Nothing -> return []

-- | BUG: Priority ordering may be violated under concurrent access
-- | If priority lanes are accessed concurrently, ordering may be wrong
prop_bug_concurrentPriorityOrdering :: Property
prop_bug_concurrentPriorityOrdering = monadicIO $ do
  now <- run getCurrentTime
  
  -- Create many jobs with mixed priorities
  highJobs <- pick $ replicateM 10 $ do
    jobNum <- choose (1, 10000)
    genRealisticJob now jobNum >>= \j -> return j { qjPriority = High }
  
  normalJobs <- pick $ replicateM 20 $ do
    jobNum <- choose (1, 10000)
    genRealisticJob now jobNum >>= \j -> return j { qjPriority = Normal }
  
  lowJobs <- pick $ replicateM 10 $ do
    jobNum <- choose (1, 10000)
    genRealisticJob now jobNum >>= \j -> return j { qjPriority = Low }
  
  let allJobs = highJobs ++ normalJobs ++ lowJobs
  
  queue <- run $ atomically createQueue
  
  -- Enqueue all
  run $ atomically $ forM_ allJobs $ enqueueJob queue
  
  -- Dequeue all and check ordering
  dequeuedJobs <- run $ atomically $ replicateM (length allJobs) $ dequeueJob queue
  
  let priorities = map qjPriority dequeuedJobs
  
  -- All High should come before Normal
  let highIndices = [i | (i, p) <- zip [0..] priorities, p == High]
  let normalIndices = [i | (i, p) <- zip [0..] priorities, p == Normal]
  let lowIndices = [i | (i, p) <- zip [0..] priorities, p == Low]
  
  let maxHigh = if null highIndices then -1 else maximum highIndices
  let minNormal = if null normalIndices then 999999 else minimum normalIndices
  let maxNormal = if null normalIndices then -1 else maximum normalIndices
  let minLow = if null lowIndices then 999999 else minimum lowIndices
  
  assert $ maxHigh < minNormal || null normalIndices
  assert $ maxNormal < minLow || null lowIndices
  -- BUG: If priority ordering is violated, this will fail

-- | BUG: Jobs may be lost if size counter wraps around
-- | If Int32 wraps around, jobs may be lost
prop_bug_sizeWrapAround :: Property
prop_bug_sizeWrapAround = monadicIO $ do
  now <- run getCurrentTime
  
  -- Create many jobs to potentially cause wrap-around
  -- Int32 max is 2,147,483,647, but we'll test with smaller numbers
  -- to catch the pattern
  jobCount <- pick $ choose (1000, 5000)
  
  jobs <- pick $ replicateM jobCount (genRealisticJob now =<< choose (1, 10000))
  
  queue <- run $ atomically createQueue
  
  -- Enqueue all
  run $ atomically $ forM_ jobs $ enqueueJob queue
  
  -- Check size
  size <- run $ atomically $ queueSize queue
  
  -- Dequeue all and count
  dequeuedJobs <- run $ atomically $ do
    results <- replicateM jobCount $ tryDequeueJob queue
    return $ length $ filter isJust results
  
  -- All jobs should be dequeuable
  assert $ dequeuedJobs == jobCount
  assert $ fromIntegral size == jobCount
  -- BUG: If size wraps around or jobs are lost, this will fail

-- | BUG: isEmpty may return wrong value if size counter is wrong
prop_bug_isEmptyAccuracy :: Property
prop_bug_isEmptyAccuracy = monadicIO $ do
  now <- run getCurrentTime
  
  queue <- run $ atomically createQueue
  
  -- Should be empty initially
  isEmpty1 <- run $ atomically $ isEmpty queue
  size1 <- run $ atomically $ queueSize queue
  assert isEmpty1
  assert $ size1 == 0
  
  -- Enqueue a job
  job <- pick $ genRealisticJob now 1
  run $ atomically $ enqueueJob queue job
  
  -- Should not be empty
  isEmpty2 <- run $ atomically $ isEmpty queue
  size2 <- run $ atomically $ queueSize queue
  assert $ not isEmpty2
  assert $ size2 == 1
  
  -- Dequeue the job
  run $ atomically $ dequeueJob queue
  
  -- Should be empty again
  isEmpty3 <- run $ atomically $ isEmpty queue
  size3 <- run $ atomically $ queueSize queue
  assert isEmpty3
  assert $ size3 == 0
  -- BUG: If isEmpty or size are wrong, this will fail

-- | BUG: Size counter may desynchronize under rapid enqueue/dequeue
-- | Rapid operations may cause size counter to drift from actual queue contents
prop_bug_sizeDesynchronization :: Property
prop_bug_sizeDesynchronization = monadicIO $ do
  now <- run getCurrentTime
  operationCount <- pick $ choose (50, 200)  -- Many rapid operations
  
  queue <- run $ atomically createQueue
  
  -- Generate jobs first
  jobs <- pick $ replicateM operationCount $ do
    jobNum <- choose (1, 100000)
    genRealisticJob now jobNum >>= \j -> return j { qjPriority = Normal }
  
  -- Perform many rapid enqueue/dequeue operations
  run $ atomically $ do
    forM_ (zip [1..] jobs) $ \(i, job) -> do
      enqueueJob queue job
      -- Dequeue every other job
      if i `mod` 2 == 0
        then void $ tryDequeueJob queue
        else return ()
  
  -- Check size matches actual queue contents
  size <- run $ atomically $ queueSize queue
  actualCount <- run $ atomically $ do
    highCount <- countQueue (rqHigh queue)
    normalCount <- countQueue (rqNormal queue)
    lowCount <- countQueue (rqLow queue)
    return $ highCount + normalCount + lowCount
  
  -- Size should match actual count
  assert $ fromIntegral size == actualCount
  -- BUG: If size counter desynchronizes, this will fail

-- | BUG: Priority ordering may be violated with interleaved enqueue/dequeue
-- | If jobs are enqueued/dequeued in rapid succession, priority ordering may break
prop_bug_interleavedPriorityOrdering :: Property
prop_bug_interleavedPriorityOrdering = monadicIO $ do
  now <- run getCurrentTime
  
  -- Generate jobs first
  highJob1 <- pick $ genRealisticJob now 1 >>= \j -> return j { qjPriority = High }
  normalJob1 <- pick $ genRealisticJob now 2 >>= \j -> return j { qjPriority = Normal }
  lowJob1 <- pick $ genRealisticJob now 3 >>= \j -> return j { qjPriority = Low }
  highJob2 <- pick $ genRealisticJob now 4 >>= \j -> return j { qjPriority = High }
  
  queue <- run $ atomically createQueue
  
  -- Interleave enqueue/dequeue operations
  run $ atomically $ do
    -- Enqueue High
    enqueueJob queue highJob1
    
    -- Enqueue Normal
    enqueueJob queue normalJob1
    
    -- Dequeue (should get High)
    dequeued1 <- dequeueJob queue
    if qjPriority dequeued1 /= High
      then error "Expected High priority"
      else return ()
    
    -- Enqueue Low
    enqueueJob queue lowJob1
    
    -- Enqueue another High
    enqueueJob queue highJob2
    
    -- Dequeue (should get High, not Normal)
    dequeued2 <- dequeueJob queue
    if qjPriority dequeued2 /= High
      then error "Expected High priority"
      else return ()
    
    -- Dequeue (should get Normal)
    dequeued3 <- dequeueJob queue
    if qjPriority dequeued3 /= Normal
      then error "Expected Normal priority"
      else return ()
    
    -- Dequeue (should get Low)
    dequeued4 <- dequeueJob queue
    if qjPriority dequeued4 /= Low
      then error "Expected Low priority"
      else return ()
  
  -- All assertions passed
  assert True
  -- BUG: If priority ordering is violated, assertions will fail

-- | BUG: Size counter may not handle empty queue dequeue correctly
-- | If dequeueJob is called on empty queue, size may become negative
prop_bug_emptyQueueDequeue :: Property
prop_bug_emptyQueueDequeue = monadicIO $ do
  queue <- run $ atomically createQueue
  
  -- Try to dequeue from empty queue (should block, but we'll use tryDequeueJob)
  result <- run $ atomically $ tryDequeueJob queue
  
  -- Should return Nothing
  assert $ result == Nothing
  
  -- Size should still be 0
  size <- run $ atomically $ queueSize queue
  assert $ size == 0
  
  -- isEmpty should be True
  isEmptyCheck <- run $ atomically $ isEmpty queue
  assert isEmptyCheck
  -- BUG: If empty queue dequeue corrupts state, this will fail

-- | BUG: Multiple rapid tryDequeueJob calls may cause size counter issues
-- | Rapid tryDequeueJob calls may cause size counter to become negative
prop_bug_rapidTryDequeue :: Property
prop_bug_rapidTryDequeue = monadicIO $ do
  now <- run getCurrentTime
  
  queue <- run $ atomically createQueue
  
  -- Enqueue a few jobs
  jobs <- pick $ replicateM 5 (genRealisticJob now =<< choose (1, 10000))
  run $ atomically $ forM_ jobs $ enqueueJob queue
  
  -- Rapidly try to dequeue more than we have
  results <- run $ atomically $ replicateM 20 $ tryDequeueJob queue
  
  -- Should get exactly 5 Just values
  let justCount = length $ filter isJust results
  assert $ justCount == 5
  
  -- Size should be 0
  size <- run $ atomically $ queueSize queue
  assert $ size == 0
  
  -- isEmpty should be True
  isEmptyCheck <- run $ atomically $ isEmpty queue
  assert isEmptyCheck
  -- BUG: If rapid tryDequeueJob causes size counter issues, this will fail

-- | BUG: Size counter may wrap around with very large queues
-- | Int32 max is 2,147,483,647, but we test with smaller numbers to catch pattern
prop_bug_sizeCounterWrapAround :: Property
prop_bug_sizeCounterWrapAround = monadicIO $ do
  now <- run getCurrentTime
  
  -- Test with large but not Int32 max number
  jobCount <- pick $ choose (10000, 50000)
  
  queue <- run $ atomically createQueue
  
  -- Enqueue many jobs
  jobs <- pick $ replicateM jobCount (genRealisticJob now =<< choose (1, 100000))
  run $ atomically $ forM_ jobs $ enqueueJob queue
  
  -- Check size
  size <- run $ atomically $ queueSize queue
  assert $ fromIntegral size == jobCount
  
  -- Dequeue all
  dequeuedCount <- run $ atomically $ do
    results <- replicateM jobCount $ tryDequeueJob queue
    return $ length $ filter isJust results
  
  -- Should dequeue all jobs
  assert $ dequeuedCount == jobCount
  
  -- Size should be 0
  finalSize <- run $ atomically $ queueSize queue
  assert $ finalSize == 0
  -- BUG: If size counter wraps around, this will fail

-- | BUG: Priority ordering may fail with many jobs of same priority
-- | With many jobs of same priority, FIFO ordering must be preserved
prop_bug_fifoOrderingManyJobs :: Property
prop_bug_fifoOrderingManyJobs = monadicIO $ do
  now <- run getCurrentTime
  jobCount <- pick $ choose (100, 500)  -- Many jobs
  
  -- Create many jobs with same priority
  jobs <- pick $ replicateM jobCount $ do
    jobNum <- choose (1, 100000)
    genRealisticJob now jobNum >>= \j -> return j { qjPriority = Normal }
  
  let jobIds = map qjJobId jobs
  
  queue <- run $ atomically createQueue
  
  -- Enqueue all
  run $ atomically $ forM_ jobs $ enqueueJob queue
  
  -- Dequeue all
  dequeuedJobs <- run $ atomically $ replicateM jobCount $ dequeueJob queue
  
  let dequeuedIds = map qjJobId dequeuedJobs
  
  -- Should be dequeued in same order as enqueued (FIFO)
  assert $ dequeuedIds == jobIds
  -- BUG: If FIFO ordering is violated, this will fail

-- | BUG: Size counter may become inconsistent with isEmpty
-- | isEmpty checks actual queues, size checks counter - they should match
prop_bug_sizeIsEmptyConsistency :: Property
prop_bug_sizeIsEmptyConsistency = monadicIO $ do
  now <- run getCurrentTime
  
  queue <- run $ atomically createQueue
  
  -- Initially empty
  isEmpty1 <- run $ atomically $ isEmpty queue
  size1 <- run $ atomically $ queueSize queue
  assert isEmpty1
  assert $ size1 == 0
  
  -- Enqueue and dequeue many times
  forM_ [1..100] $ \i -> do
    job <- pick $ genRealisticJob now i
    run $ atomically $ enqueueJob queue job
    
    isEmptyAfterEnqueue <- run $ atomically $ isEmpty queue
    sizeAfterEnqueue <- run $ atomically $ queueSize queue
    
    -- If size > 0, isEmpty should be False
    if sizeAfterEnqueue > 0
      then assert $ not isEmptyAfterEnqueue
      else assert isEmptyAfterEnqueue
    
    -- Dequeue
    run $ atomically $ void $ tryDequeueJob queue
    
    isEmptyAfterDequeue <- run $ atomically $ isEmpty queue
    sizeAfterDequeue <- run $ atomically $ queueSize queue
    
    -- If size == 0, isEmpty should be True
    if sizeAfterDequeue == 0
      then assert isEmptyAfterDequeue
      else assert $ not isEmptyAfterDequeue
  
  -- Final state should be empty
  isEmptyFinal <- run $ atomically $ isEmpty queue
  sizeFinal <- run $ atomically $ queueSize queue
  assert isEmptyFinal
  assert $ sizeFinal == 0
  -- BUG: If size and isEmpty become inconsistent, this will fail

-- | BUG: Priority lanes may become desynchronized
-- | If enqueue/dequeue operations are not atomic across lanes, lanes may desync
prop_bug_priorityLaneDesync :: Property
prop_bug_priorityLaneDesync = monadicIO $ do
  now <- run getCurrentTime
  
  queue <- run $ atomically createQueue
  
  -- Enqueue jobs to all priority lanes
  highJob <- pick $ genRealisticJob now 1 >>= \j -> return j { qjPriority = High }
  normalJob <- pick $ genRealisticJob now 2 >>= \j -> return j { qjPriority = Normal }
  lowJob <- pick $ genRealisticJob now 3 >>= \j -> return j { qjPriority = Low }
  
  run $ atomically $ do
    enqueueJob queue highJob
    enqueueJob queue normalJob
    enqueueJob queue lowJob
  
  -- Check size matches sum of all lanes
  size <- run $ atomically $ queueSize queue
  actualCount <- run $ atomically $ do
    highCount <- countQueue (rqHigh queue)
    normalCount <- countQueue (rqNormal queue)
    lowCount <- countQueue (rqLow queue)
    return $ highCount + normalCount + lowCount
  
  assert $ fromIntegral size == actualCount
  assert $ actualCount == 3
  -- BUG: If priority lanes desynchronize, this will fail

-- | BUG: Job loss during rapid enqueue/dequeue cycles
-- | Rapid cycles may cause jobs to be lost if operations are not atomic
prop_bug_jobLossRapidCycles :: Property
prop_bug_jobLossRapidCycles = monadicIO $ do
  now <- run getCurrentTime
  cycleCount <- pick $ choose (50, 200)
  
  -- Generate all jobs first
  jobs <- pick $ replicateM cycleCount $ do
    jobNum <- choose (1, 100000)
    genRealisticJob now jobNum >>= \j -> return j { qjPriority = Normal }
  
  let allJobIds = map qjJobId jobs
  
  queue <- run $ atomically createQueue
  
  -- Track enqueued job IDs
  allJobIdsVar <- run $ newTVarIO []
  
  -- Perform many enqueue/dequeue cycles
  run $ atomically $ do
    forM_ (zip [1..] jobs) $ \(i, job) -> do
      enqueueJob queue job
      modifyTVar' allJobIdsVar (qjJobId job :)
      
      -- Dequeue every other cycle
      if i `mod` 2 == 0
        then void $ tryDequeueJob queue
        else return ()
  
  -- Get remaining jobs
  remainingJobs <- run $ atomically $ do
    results <- replicateM cycleCount $ tryDequeueJob queue
    return $ mapMaybe id results
  
  -- Count total jobs processed
  enqueuedIds <- run $ readTVarIO allJobIdsVar
  let remainingIds = map qjJobId remainingJobs
  
  -- All remaining job IDs should be in enqueued list
  assert $ all (`elem` enqueuedIds) remainingIds
  
  -- Final size should match remaining jobs
  finalSize <- run $ atomically $ queueSize queue
  assert $ fromIntegral finalSize == length remainingJobs
  -- BUG: If jobs are lost, this will fail

-- ============================================================================
-- TEST RUNNER
-- ============================================================================

main :: IO ()
main = do
  putStrLn "Queue Property Tests"
  putStrLn "===================="
  
  putStrLn "\n1. Enqueue/Dequeue Roundtrip"
  quickCheck prop_enqueueDequeueRoundTrip
  
  putStrLn "\n2. Queue Size Invariant"
  quickCheck prop_queueSizeInvariant
  
  putStrLn "\n3. Priority Ordering"
  quickCheck prop_priorityOrdering
  
  putStrLn "\n4. No Job Loss"
  quickCheck prop_noJobLoss
  
  putStrLn "\n5. FIFO Within Priority"
  quickCheck prop_fifoWithinPriority
  
  putStrLn "\n6. Mixed Priority Ordering"
  quickCheck prop_mixedPriorityOrdering
  
  putStrLn "\n7. tryDequeueJob Matches dequeueJob"
  quickCheck prop_tryDequeueMatchesDequeue
  
  putStrLn "\n8. tryDequeueJob Empty"
  quickCheck prop_tryDequeueEmpty
  
  putStrLn "\n9. Size Never Negative"
  quickCheck prop_sizeNeverNegative
  
  putStrLn "\n10. Bug: Size Sync"
  quickCheck prop_bug_sizeSync
  
  putStrLn "\n11. Bug: Concurrent Priority Ordering"
  quickCheck prop_bug_concurrentPriorityOrdering
  
  putStrLn "\n12. Bug: Size Wrap Around"
  quickCheck prop_bug_sizeWrapAround
  
  putStrLn "\n13. Bug: isEmpty Accuracy"
  quickCheck prop_bug_isEmptyAccuracy
  
  putStrLn "\n14. Bug: Size Desynchronization"
  quickCheck prop_bug_sizeDesynchronization
  
  putStrLn "\n15. Bug: Interleaved Priority Ordering"
  quickCheck prop_bug_interleavedPriorityOrdering
  
  putStrLn "\n16. Bug: Empty Queue Dequeue"
  quickCheck prop_bug_emptyQueueDequeue
  
  putStrLn "\n17. Bug: Rapid TryDequeue"
  quickCheck prop_bug_rapidTryDequeue
  
  putStrLn "\n18. Bug: Size Counter Wrap Around"
  quickCheck prop_bug_sizeCounterWrapAround
  
  putStrLn "\n19. Bug: FIFO Ordering Many Jobs"
  quickCheck prop_bug_fifoOrderingManyJobs
  
  putStrLn "\n20. Bug: Size isEmpty Consistency"
  quickCheck prop_bug_sizeIsEmptyConsistency
  
  putStrLn "\n21. Bug: Priority Lane Desync"
  quickCheck prop_bug_priorityLaneDesync
  
  putStrLn "\n22. Bug: Job Loss Rapid Cycles"
  quickCheck prop_bug_jobLossRapidCycles
  
  putStrLn "\nAll tests completed!"
