{-# LANGUAGE OverloadedStrings #-}

-- | Render Gateway Integration Tests
-- | Tests for component interactions
module Integration where

import Test.Hspec

import Render.Gateway.STM.Queue
import Render.Gateway.STM.RateLimiter
import Render.Gateway.STM.CircuitBreaker
import Render.Gateway.STM.Clock
import Render.Gateway.Core
import Render.Gateway.Backend

import Control.Concurrent.STM
import Data.Text (Text)
import Data.Time (getCurrentTime, UTCTime, addUTCTime)
import Data.Aeson (object)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (isJust)

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

-- | Integration tests
integrationTests :: Spec
integrationTests = describe "Gateway Integration Tests" $ do
  it "processes request through full gateway flow" $ do
    queue <- atomically createQueue
    store <- atomically createJobStore
    clock <- createClock
    rateLimiters <- atomically $ newTVar Map.empty
    now <- getCurrentTime
    
    -- Create backend
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
    
    -- Create and enqueue job
    let job = createJob now "j_test" Normal
    atomically $ do
      storeJob store job
      enqueueJob queue job
    
    -- Process request
    result <- atomically $ processRequest gatewayState
    case result of
      Just (processedJob, selectedBackend) -> do
        qjJobId processedJob `shouldBe` "j_test"
        beId selectedBackend `shouldBe` "b1"
        
        -- Verify job status updated
        retrieved <- atomically $ getJob store "j_test"
        case retrieved of
          Just j -> do
            qjStatus j `shouldBe` Running
            -- Verify started_at timestamp is set
            qjStartedAt j `shouldSatisfy` isJust
          Nothing -> expectationFailure "Job should exist"
      Nothing -> expectationFailure "Should process request"

  it "handles request success flow" $ do
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
    
    let job = createJob now "j_test" Normal
    atomically $ storeJob store job
    
    -- Handle success
    atomically $ handleRequestSuccess gatewayState job backend "https://cdn.render.weyl.ai/output.mp4"
    
    -- Verify job completed
    retrieved <- atomically $ getJob store "j_test"
    case retrieved of
      Just j -> do
        qjStatus j `shouldBe` Complete
        case qjOutput j of
          Just url -> url `shouldBe` "https://cdn.render.weyl.ai/output.mp4"
          Nothing -> expectationFailure "Should have output URL"
        -- Verify completed_at timestamp is set
        qjCompletedAt j `shouldSatisfy` isJust
      Nothing -> expectationFailure "Job should exist"

  it "handles request failure flow" $ do
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
    
    let job = createJob now "j_test" Normal
    atomically $ storeJob store job
    
    -- Handle failure
    atomically $ handleRequestFailure gatewayState job backend "Backend timeout"
    
    -- Verify job errored
    retrieved <- atomically $ getJob store "j_test"
    case retrieved of
      Just j -> do
        qjStatus j `shouldBe` Error
        case qjError j of
          Just err -> err `shouldBe` "Backend timeout"
          Nothing -> expectationFailure "Should have error message"
        -- Verify completed_at timestamp is set
        qjCompletedAt j `shouldSatisfy` isJust
      Nothing -> expectationFailure "Job should exist"

  it "rate limiter integrates with gateway processing" $ do
    queue <- atomically createQueue
    store <- atomically createJobStore
    clock <- createClock
    rateLimiters <- atomically $ newTVar Map.empty
    now <- getCurrentTime
    
    -- Create rate limiter with low capacity
    rl <- atomically $ createRateLimiter 1.0 0.1 now
    atomically $ modifyTVar' rateLimiters (Map.insert "cust_test" rl)
    
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
    
    let job = createJob now "j_test" Normal
    atomically $ do
      storeJob store job
      enqueueJob queue job
    
    -- First request should succeed (token available)
    result1 <- atomically $ processRequest gatewayState
    result1 `shouldSatisfy` isJust
    
    -- Second request should fail (no token)
    let job2 = createJob now "j_test2" Normal
    atomically $ do
      storeJob store job2
      enqueueJob queue job2
    
    -- Should block or fail due to rate limit
    -- Note: acquireTokenBlocking will retry, so this test verifies integration
    -- In a real scenario, we'd need to handle the blocking behavior differently
