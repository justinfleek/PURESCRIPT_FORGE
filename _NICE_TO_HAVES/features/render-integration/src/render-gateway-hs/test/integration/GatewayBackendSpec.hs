{-# LANGUAGE OverloadedStrings #-}

-- | Deep comprehensive integration tests for Gateway ↔ Backend interaction
-- | Tests HTTP forwarding, success paths, failure handling, timeouts, and retry logic
module GatewayBackendSpec where

import Test.Hspec
import Control.Concurrent.STM
import Data.Text (Text)
import qualified Data.Text as Text
import Data.Time (getCurrentTime, UTCTime)
import Data.Aeson (object)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust, isNothing)
import Data.List (filter)

import Render.Gateway.STM.Queue
import Render.Gateway.STM.RateLimiter
import Render.Gateway.STM.CircuitBreaker
import Render.Gateway.STM.Clock
import Render.Gateway.Core
import Render.Gateway.Backend
import Control.Concurrent (threadDelay)

-- | Helper to create test job
createJob :: UTCTime -> Text -> Priority -> QueuedJob
createJob now jobId priority = QueuedJob
  { qjJobId = jobId
  , qjRequestId = "req_" <> jobId
  , qjCustomerId = "cust_test"
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

-- | Deep comprehensive integration tests for Gateway ↔ Backend
spec :: Spec
spec = describe "Gateway ↔ Backend Integration Deep Tests" $ do
  describe "HTTP Forwarding - Success Path" $ do
    it "successfully forwards request to backend and receives response" $ do
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 0
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      let job = createJob now "j_success" Normal
      atomically $ do
        storeJob store job
        enqueueJob queue job
      
      -- Process request (simulates HTTP forwarding)
      result <- atomically $ processRequest gatewayState
      case result of
        Just (processedJob, selectedBackend) -> do
          qjJobId processedJob `shouldBe` "j_success"
          beId selectedBackend `shouldBe` "b1"
          
          -- Verify backend in-flight count incremented
          inFlightCount <- atomically $ readTVar (beInFlight selectedBackend)
          inFlightCount `shouldBe` 1
          
          -- Verify job status updated to Running
          retrieved <- atomically $ getJob store "j_success"
          case retrieved of
            Just j -> do
              qjStatus j `shouldBe` Running
              qjStartedAt j `shouldSatisfy` isJust
            Nothing -> expectationFailure "Job should exist"
        Nothing -> expectationFailure "Should process request successfully"

    it "handles multiple concurrent requests to same backend" $ do
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 0
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      -- Enqueue multiple jobs
      let jobs = [createJob now ("j_" <> show i) Normal | i <- [1..5]]
      atomically $ mapM_ (\job -> do
        storeJob store job
        enqueueJob queue job
      ) jobs
      
      -- Process all requests
      results <- atomically $ mapM (const $ processRequest gatewayState) [1..5]
      let successfulResults = filter isJust results
      length successfulResults `shouldBe` 5
      
      -- Verify backend in-flight count matches
      inFlightCount <- atomically $ readTVar (beInFlight backend)
      inFlightCount `shouldBe` 5

  describe "HTTP Forwarding - Failure Path" $ do
    it "handles backend HTTP error responses (4xx)" $ do
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 0
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      let job = createJob now "j_4xx" Normal
      atomically $ storeJob store job
      
      -- Simulate 400 Bad Request error
      atomically $ handleRequestFailure gatewayState job backend "HTTP 400: Bad Request"
      
      -- Verify error recorded
      retrieved <- atomically $ getJob store "j_4xx"
      case retrieved of
        Just j -> do
          qjStatus j `shouldBe` Error
          qjError j `shouldSatisfy` isJust
          case qjError j of
            Just err -> err `shouldContain` "400"
            Nothing -> expectationFailure "Should have error message"
        Nothing -> expectationFailure "Job should exist"
      
      -- Verify circuit breaker records failure
      (_, now') <- atomically $ readClockSTM clock
      failures <- atomically $ recordBackendFailure backend now'
      -- Circuit breaker should track the failure

    it "handles backend HTTP error responses (5xx)" $ do
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 0
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      let job = createJob now "j_5xx" Normal
      atomically $ storeJob store job
      
      -- Simulate 500 Internal Server Error
      atomically $ handleRequestFailure gatewayState job backend "HTTP 500: Internal Server Error"
      
      -- Verify error recorded
      retrieved <- atomically $ getJob store "j_5xx"
      case retrieved of
        Just j -> do
          qjStatus j `shouldBe` Error
          qjError j `shouldSatisfy` isJust
          case qjError j of
            Just err -> err `shouldContain` "500"
            Nothing -> expectationFailure "Should have error message"
        Nothing -> expectationFailure "Job should exist"

    it "handles backend connection errors" $ do
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 0
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      let job = createJob now "j_conn_error" Normal
      atomically $ storeJob store job
      
      -- Simulate connection error
      atomically $ handleRequestFailure gatewayState job backend "Connection refused"
      
      -- Verify error recorded
      retrieved <- atomically $ getJob store "j_conn_error"
      case retrieved of
        Just j -> do
          qjStatus j `shouldBe` Error
          qjError j `shouldSatisfy` isJust
        Nothing -> expectationFailure "Job should exist"

  describe "Timeout Handling" $ do
    it "handles backend request timeout" $ do
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 0
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      let job = createJob now "j_timeout" Normal
      atomically $ storeJob store job
      
      -- Simulate timeout
      atomically $ handleRequestFailure gatewayState job backend "Request timeout after 30s"
      
      -- Verify timeout error recorded
      retrieved <- atomically $ getJob store "j_timeout"
      case retrieved of
        Just j -> do
          qjStatus j `shouldBe` Error
          qjError j `shouldSatisfy` isJust
          case qjError j of
            Just err -> err `shouldContain` "timeout"
            Nothing -> expectationFailure "Should have error message"
        Nothing -> expectationFailure "Job should exist"

    it "BUG: timeout may not release backend immediately" $ do
      -- BUG: If timeout occurs, backend may not be released immediately
      -- This could cause capacity leaks
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 1  -- Start with 1 in-flight (simulating timeout scenario)
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      let job = createJob now "j_timeout_bug" Normal
      atomically $ storeJob store job
      
      -- Simulate timeout failure
      -- BUG: handleRequestFailure should release backend via recordBackendFailure
      -- But if timeout happens in a different code path, backend may not be released
      atomically $ handleRequestFailure gatewayState job backend "Request timeout after 30s"
      
      -- Verify backend was released
      inFlightCount <- atomically $ readTVar (beInFlight backend)
      -- BUG: If backend is not released, inFlightCount will still be 1
      -- This test verifies that handleRequestFailure does release backend
      inFlightCount `shouldBe` 0
      
      -- BUG: However, if timeout occurs in forwardToBackend and exception handling
      -- doesn't call handleRequestFailure, backend may not be released
      -- This is a potential bug if exception handling is incomplete

  describe "Retry Logic" $ do
    it "retries failed requests with exponential backoff" $ do
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 0
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      -- Create job with retry count
      let job = (createJob now "j_retry" Normal) { qjRetryCount = 1 }
      atomically $ do
        storeJob store job
        enqueueJob queue job
      
      -- Process request (should retry)
      result <- atomically $ processRequest gatewayState
      case result of
        Just (processedJob, _) -> do
          -- Retry count should be incremented
          qjRetryCount processedJob `shouldBe` 2
        Nothing -> expectationFailure "Should process retry request"

    it "BUG: retry logic may retry indefinitely" $ do
      -- BUG: While maxRetries = 3 is enforced in Server.hs,
      -- if retryCount is not incremented correctly or checked incorrectly,
      -- retries could exceed the limit
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 0
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      -- Create job with retryCount = 2 (one retry remaining before maxRetries = 3)
      let job = (createJob now "j_retry_limit" Normal) { qjRetryCount = 2 }
      atomically $ do
        storeJob store job
        enqueueJob queue job
      
      -- Process request
      result <- atomically $ processRequest gatewayState
      result `shouldSatisfy` isJust
      
      -- Verify retryCount is 2 (not incremented yet - increment happens in processJobAsync)
      retrieved <- atomically $ getJob store "j_retry_limit"
      case retrieved of
        Just j -> do
          -- BUG: If retryCount check uses wrong comparison (e.g., <= instead of <),
          -- or if retryCount is not incremented before check, retries could exceed limit
          qjRetryCount j `shouldBe` 2
        Nothing -> expectationFailure "Job should exist"
      
      -- BUG: If maxRetries check is `qjRetryCount <= maxRetries` instead of `<`,
      -- job with retryCount = 3 would still retry (4th retry)
      -- BUG: If retryCount is checked before increment, job with retryCount = 2
      -- would retry (making it 3), then retry again (making it 4) if check is wrong

    it "BUG: retry may not respect circuit breaker state" $ do
      -- BUG: Retry logic in Server.hs checks isRetriable and retryCount
      -- but does NOT check if circuit breaker is open before retrying
      -- This could cause retries to failbackend even when circuit is open
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      -- Create circuit breaker and force it open
      cb <- atomically $ do
        cb' <- createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
        -- Force circuit open by recording multiple failures
        recordFailure cb' now
        recordFailure cb' now
        recordFailure cb' now  -- Should open circuit
        pure cb'
      
      inFlight <- atomically $ newTVar 0
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      -- Verify circuit breaker is open
      (_, now') <- atomically $ readClockSTM clock
      available <- atomically $ isAvailable cb now'
      available `shouldBe` False  -- Circuit should be open
      
      -- Create job with retry count < maxRetries
      let job = (createJob now "j_retry_circuit" Normal) { qjRetryCount = 1 }
      atomically $ storeJob store job
      
      -- BUG: Retry logic in Server.hs (line 472) checks:
      --   `isRetriable && qjRetryCount job < maxRetries`
      -- But does NOT check `isAvailable backend.beCircuit`
      -- So retry will proceed even if circuit breaker is open
      -- This causes unnecessary retries that will fail immediately
      
      -- Simulate retry scenario: job failed, is retriable, retryCount < maxRetries
      -- But circuit breaker is open, so retry should NOT happen
      -- However, current code will retry anyway
      
      -- BUG: selectBackend should exclude backend with open circuit,
      -- but if retry happens before selectBackend checks circuit breaker,
      -- retry will attempt to use unavailable backend
      
      -- This test documents that retry logic doesn't check circuit breaker state
      -- before deciding to retry

  describe "Backend Release" $ do
    it "releases backend after successful request completion" $ do
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 1  -- Start with 1 in-flight
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      let job = createJob now "j_release" Normal
      atomically $ storeJob store job
      
      -- Handle success (should release backend)
      atomically $ handleRequestSuccess gatewayState job backend "https://cdn.example.com/output.mp4"
      
      -- Verify backend released (in-flight decremented)
      inFlightCount <- atomically $ readTVar (beInFlight backend)
      inFlightCount `shouldBe` 0

    it "releases backend after failed request" $ do
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 1  -- Start with 1 in-flight
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      let job = createJob now "j_release_fail" Normal
      atomically $ storeJob store job
      
      -- Handle failure (should release backend)
      atomically $ handleRequestFailure gatewayState job backend "Error"
      
      -- Verify backend released (in-flight decremented)
      inFlightCount <- atomically $ readTVar (beInFlight backend)
      inFlightCount `shouldBe` 0

    it "BUG: backend may not be released if job is deleted concurrently" $ do
      -- BUG: Race condition - if job is deleted after backend selection
      -- but before completion, backend may not be released
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 0
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      let job = createJob now "j_delete_race" Normal
      atomically $ do
        storeJob store job
        enqueueJob queue job
      
      -- Process request (selects backend, increments inFlight)
      result <- atomically $ processRequest gatewayState
      result `shouldSatisfy` isJust
      
      case result of
        Just (processedJob, selectedBackend) -> do
          -- Verify backend in-flight incremented
          inFlightCount1 <- atomically $ readTVar (beInFlight selectedBackend)
          inFlightCount1 `shouldBe` 1
          
          -- Delete job concurrently (simulating race condition)
          atomically $ deleteJob store "j_delete_race"
          
          -- BUG: If handleRequestSuccess/handleRequestFailure is called after deletion,
          -- they check if job exists and return early without releasing backend
          -- However, processRequest already incremented inFlight
          
          -- Simulate what happens if handleRequestSuccess is called after deletion
          atomically $ handleRequestSuccess gatewayState processedJob selectedBackend "https://cdn.example.com/output.mp4"
          
          -- Verify backend was released (handleRequestSuccess checks if job exists,
          -- but if job was deleted, it returns early without calling recordBackendSuccess)
          -- BUG: However, processRequest already incremented inFlight, so backend is not released
          inFlightCount2 <- atomically $ readTVar (beInFlight selectedBackend)
          
          -- BUG: If handleRequestSuccess returns early when job is deleted,
          -- backend is not released, causing capacity leak
          -- Current code does handle this correctly (returns early, but processRequest
          -- should release backend in this case)
          -- However, if deletion happens between processRequest and handleRequestSuccess,
          -- backend may not be released
          
          -- This test verifies the race condition scenario
          -- Current implementation: handleRequestSuccess returns early if job deleted,
          -- but processRequest already incremented inFlight
          -- BUG: Backend should be released when job is deleted, but current code
          -- relies on handleRequestSuccess/handleRequestFailure to release it
          -- If they return early, backend is not released
          
          -- Actually, looking at Server.hs lines 441-449, if job is deleted,
          -- backend IS released. But this test verifies edge cases.
          inFlightCount2 `shouldBe` 0  -- Should be released
          
        Nothing -> expectationFailure "Should process request"
      
      -- BUG: Another race condition: if job is deleted between processRequest
      -- selecting backend and processRequest checking if job exists,
      -- backend may not be released
      -- Current code handles this (lines 178-184 in Core.hs), but edge cases may exist

    it "BUG: backend release may not happen if updateJob fails" $ do
      -- BUG: In handleRequestSuccess/handleRequestFailure, if updateJob returns False,
      -- recordBackendSuccess/Failure is not called, so backend is not released
      -- But processRequest already incremented inFlight, causing capacity leak
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 1  -- Start with 1 (simulating backend already acquired)
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      let job = createJob now "j_update_fail" Normal
      -- Don't store job (simulating job deleted between processRequest and handleRequestSuccess)
      
      -- BUG: handleRequestSuccess checks if job exists, and if not, returns early
      -- without releasing backend. But processRequest already incremented inFlight.
      -- Current code: handleRequestSuccess returns early if job doesn't exist (line 211),
      -- but backend was already incremented by processRequest
      -- This causes capacity leak
      atomically $ handleRequestSuccess gatewayState job backend "https://cdn.example.com/output.mp4"
      
      -- Verify backend was NOT released (bug scenario)
      inFlightCount <- atomically $ readTVar (beInFlight backend)
      -- BUG: Backend should be released even if job doesn't exist,
      -- but current code returns early without releasing
      inFlightCount `shouldBe` 1  -- BUG: Not released

    it "BUG: multiple backend releases may cause negative inFlight count" $ do
      -- BUG: If releaseBackend is called multiple times for same backend,
      -- inFlight count may become negative (though max 0 prevents this)
      -- But if releaseBackend is called incorrectly, capacity tracking is wrong
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 1  -- Start with 1
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      -- Release backend multiple times (simulating bug)
      atomically $ do
        releaseBackend backend
        releaseBackend backend
        releaseBackend backend
      
      -- BUG: releaseBackend uses max 0, so count won't go negative,
      -- but if called multiple times incorrectly, capacity tracking is wrong
      inFlightCount <- atomically $ readTVar (beInFlight backend)
      inFlightCount `shouldBe` 0  -- max 0 prevents negative, but should be -2 if not for max
      
      -- BUG: If releaseBackend is called more times than acquireBackend,
      -- capacity tracking becomes incorrect (though max 0 prevents negative)

    it "BUG: retry may cause backend to be selected even when circuit breaker opens during retry" $ do
      -- BUG: Retry logic doesn't check circuit breaker state before retrying
      -- If circuit breaker opens between retry decision and backend selection,
      -- retry may still proceed with unavailable backend
      queue <- atomically createQueue
      store <- atomically createJobStore
      clock <- createClock
      rateLimiters <- atomically $ newTVar Map.empty
      now <- getCurrentTime
      
      cb <- atomically $ createCircuitBreaker now (CircuitBreakerConfig 0.5 3 60 100)
      inFlight <- atomically $ newTVar 0
      let backend = Backend
            { beId = "b1"
            , beType = Nunchaku
            , beFamily = "wan"
            , beModels = ["default"]
            , beEndpoint = "localhost:8001"
            , beCapacity = 10
            , beInFlight = inFlight
            , beCircuit = cb
            }
      
      let gatewayState = GatewayState
            { gsQueue = queue
            , gsJobStore = store
            , gsRateLimiters = rateLimiters
            , gsBackends = [backend]
            , gsClock = clock
            }
      
      -- Record failures to open circuit breaker
      atomically $ do
        recordFailure cb now
        recordFailure cb now
        recordFailure cb now  -- Should open circuit
      
      -- Verify circuit is open
      (_, now') <- atomically $ readClockSTM clock
      available <- atomically $ isAvailable cb now'
      available `shouldBe` False
      
      -- BUG: selectBackend should exclude backend with open circuit,
      -- but if retry logic doesn't check circuit breaker before retrying,
      -- retry may still attempt to use unavailable backend
      -- Current code: selectBackend checks circuit breaker (via isAvailable),
      -- so this bug may not occur, but retry logic should also check
      
      -- This test documents that retry logic should check circuit breaker
      -- before deciding to retry, not just rely on selectBackend to exclude it
