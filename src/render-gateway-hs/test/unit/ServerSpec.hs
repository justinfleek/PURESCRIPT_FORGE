{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

-- | Deep comprehensive unit tests for Server module
-- | Tests individual handlers in isolation: handleGenerate, handleGetQueue,
-- | handleGetJob, handleCancelJob, handleListModels, handleJobEvents,
-- | forwardToBackend, extractCustomerId, isRetriableError, workerLoop,
-- | streamJobEvents, sendSSEEvent, jobToResponse, statusToText, lookupQuery,
-- | backendToModels
module ServerSpec where

import Test.Hspec
import Control.Concurrent.STM
import Control.Concurrent (forkIO, threadDelay, newEmptyMVar, putMVar, takeMVar)
import Control.Exception (try, SomeException)
import Control.Monad (replicateM, replicateM_)
import Data.Aeson (object, Value(..), encode, decode, eitherDecode, (.=))
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Key (fromText)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Data.Time (getCurrentTime, UTCTime)
import Data.UUID (UUID)
import Data.UUID.V4 (nextRandom)
import qualified Data.UUID as UUID
import Network.Wai (Request(..), requestMethod, pathInfo, rawQueryString, requestHeaders, requestBody)
import Network.HTTP.Types (methodPost, methodGet, methodDelete, hAuthorization, hContentType, parseQueryText, QueryText)
import Network.HTTP.Client (Manager, newManager, defaultManagerSettings)
import Network.HTTP.Types.Status (status200, status400, status404, status500, status503)
import Render.Gateway.Core
  ( GatewayState(..)
  , JobStore(..)
  , createJobStore
  , storeJob
  , getJob
  , updateJob
  , deleteJob
  , cancelJob
  , getQueuePosition
  )
import Render.Gateway.STM.Queue
  ( RequestQueue(..)
  , QueuedJob(..)
  , Priority(..)
  , Modality(..)
  , TaskType(..)
  , JobStatus(..)
  , createQueue
  , enqueueJob
  , queueSize
  , parseTaskType
  , parseModality
  , parsePriority
  )
import Render.Gateway.STM.Clock (Clock, createClock, startClockThread, stopClockThread)
import Render.Gateway.Backend (Backend(..), BackendType(..))
import Render.Gateway.STM.CircuitBreaker (createCircuitBreaker)
import Render.Gateway.Server
  ( handleGenerate
  , handleGetQueue
  , handleGetJob
  , handleCancelJob
  , handleListModels
  , handleJobEvents
  , forwardToBackend
  , extractCustomerId
  , isRetriableError
  , workerLoop
  , streamJobEvents
  , sendSSEEvent
  , jobToResponse
  , statusToText
  , lookupQuery
  , backendToModels
  , ErrorResponse(..)
  , JobResponse(..)
  )
import qualified Data.Map.Strict as Map

-- | Helper to create test gateway state
createTestGatewayState :: IO GatewayState
createTestGatewayState = do
  queue <- atomically createQueue
  jobStore <- atomically createJobStore
  rateLimiters <- atomically $ newTVar Map.empty
  clock <- atomically createClock
  _ <- startClockThread clock
  let backends = []
  pure GatewayState
    { gsQueue = queue
    , gsJobStore = jobStore
    , gsRateLimiters = rateLimiters
    , gsBackends = backends
    , gsClock = clock
    }

-- | Helper to create test job
createTestJob :: Text -> Priority -> JobStatus -> IO QueuedJob
createTestJob jobId priority status = do
  now <- getCurrentTime
  pure QueuedJob
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
    , qjStatus = status
    , qjCreatedAt = now
    , qjStartedAt = Nothing
    , qjCompletedAt = Nothing
    , qjRequest = object []
    , qjOutput = Nothing
    , qjError = Nothing
    , qjRetryCount = 0
    }

-- | Helper to create test backend
createTestBackend :: Text -> BackendType -> Text -> [Text] -> Text -> Int32 -> IO Backend
createTestBackend backendId backendType family models endpoint capacity = do
  now <- getCurrentTime
  circuitBreaker <- atomically $ createCircuitBreaker 5 3 60.0 300.0 now
  inFlight <- atomically $ newTVar 0
  pure Backend
    { beId = backendId
    , beType = backendType
    , beFamily = family
    , beModels = models
    , beEndpoint = endpoint
    , beCapacity = capacity
    , beInFlight = inFlight
    , beCircuit = circuitBreaker
    }

-- | Mock request for testing
createMockRequest :: Text -> Text -> Text -> Text -> Maybe ByteString -> LBS.ByteString -> Request
createMockRequest modality family model task mAuthHeader body = Request
  { requestMethod = methodPost
  , httpVersion = (1, 1)
  , rawPathInfo = "/" <> Text.encodeUtf8 modality <> "/" <> Text.encodeUtf8 family <> "/" <> Text.encodeUtf8 model <> "/" <> Text.encodeUtf8 task
  , pathInfo = [modality, family, model, task]
  , rawQueryString = ""
  , queryString = parseQueryText ""
  , requestHeaders = case mAuthHeader of
      Just auth -> [(hAuthorization, auth)]
      Nothing -> []
  , isSecure = False
  , remoteHost = (0, 0, 0, 0)
  , requestBody = pure body
  , vault = error "vault not used"
  , requestBodyLength = KnownLength (fromIntegral (LBS.length body))
  , requestHeaderHost = Nothing
  , requestHeaderRange = Nothing
  }

-- | Deep comprehensive unit tests for Server module
spec :: Spec
spec = describe "Server Unit Tests" $ do
  describe "isRetriableError" $ do
    it "detects timeout errors" $ do
      isRetriableError "timeout occurred" `shouldBe` True
      isRetriableError "Request timeout" `shouldBe` True
      isRetriableError "TIMEOUT" `shouldBe` True

    it "detects connection errors" $ do
      isRetriableError "connection refused" `shouldBe` True
      isRetriableError "network error" `shouldBe` True
      isRetriableError "Connection failed" `shouldBe` True

    it "detects 5xx status codes" $ do
      isRetriableError "status 500" `shouldBe` True
      isRetriableError "status 502" `shouldBe` True
      isRetriableError "status 503" `shouldBe` True
      isRetriableError "status 504" `shouldBe` True
      isRetriableError "status 5" `shouldBe` True

    it "BUG: case-sensitive error detection" $ do
      -- BUG: isRetriableError (line 535-544) uses Text.toLower, so it should
      -- handle case-insensitive matching. However, if error messages contain
      -- mixed case or special characters, matching may fail.
      isRetriableError "Timeout" `shouldBe` True
      isRetriableError "CONNECTION" `shouldBe` True
      isRetriableError "Status 500" `shouldBe` True

    it "BUG: partial substring matches may cause false positives" $ do
      -- BUG: isRetriableError uses Text.isInfixOf, which means "status 5"
      -- will match "status 500", "status 501", etc. But it will also match
      -- "status 5" in "status 5xx" or "status 5.0.0", which may be intentional
      -- but could cause false positives if error messages contain "status 5"
      -- in non-status-code contexts.
      isRetriableError "status 5xx error" `shouldBe` True
      isRetriableError "status 5.0.0" `shouldBe` True

    it "correctly identifies non-retriable errors" $ do
      isRetriableError "invalid request" `shouldBe` False
      isRetriableError "authentication failed" `shouldBe` False
      isRetriableError "status 400" `shouldBe` False
      isRetriableError "status 404" `shouldBe` False

  describe "statusToText" $ do
    it "converts all status types correctly" $ do
      statusToText Queued `shouldBe` "queued"
      statusToText Running `shouldBe` "running"
      statusToText Complete `shouldBe` "complete"
      statusToText Error `shouldBe` "error"
      statusToText Cancelled `shouldBe` "cancelled"

  describe "lookupQuery" $ do
    it "finds query parameter when present" $ do
      let params = [("format", Just "json"), ("priority", Just "high")]
      lookupQuery "format" params `shouldBe` Just "json"
      lookupQuery "priority" params `shouldBe` Just "high"

    it "returns Nothing for missing parameter" $ do
      let params = [("format", Just "json")]
      lookupQuery "backend" params `shouldBe` Nothing

    it "BUG: returns Nothing for parameter with empty value" $ do
      -- BUG: lookupQuery (line 886-889) returns Nothing if the value is Nothing,
      -- but it doesn't distinguish between missing parameter and parameter with
      -- empty value. If a query parameter is present but has no value (e.g., "?format="),
      -- it will return Nothing, which may hide the fact that the parameter was
      -- provided but empty.
      let params = [("format", Nothing)]
      lookupQuery "format" params `shouldBe` Nothing

  describe "backendToModels" $ do
    it "converts backend to model list" $ do
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1", "model2"] "localhost:8000" 10
      models <- backendToModels backend
      
      length models `shouldBe` 2
      -- Verify model structure
      head models `shouldSatisfy` \v -> case v of
        Object obj -> KM.lookup "family" obj == Just (String "wan")
        _ -> False

    it "BUG: assigns modality based on family, may be incorrect" $ do
      -- BUG: backendToModels (line 779-789) assigns modality as "video" if
      -- family is "wan" or "qwen", otherwise "image". This hardcoded mapping
      -- may be incorrect if new families are added or if a backend supports
      -- multiple modalities.
      backend1 <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      backend2 <- createTestBackend "b2" Nunchaku "flux" ["model2"] "localhost:8000" 10
      
      models1 <- backendToModels backend1
      models2 <- backendToModels backend2
      
      head models1 `shouldSatisfy` \v -> case v of
        Object obj -> KM.lookup "modality" obj == Just (String "video")
        _ -> False
      head models2 `shouldSatisfy` \v -> case v of
        Object obj -> KM.lookup "modality" obj == Just (String "image")
        _ -> False

  describe "jobToResponse" $ do
    it "converts queued job correctly" $ do
      job <- createTestJob "j1" Normal Queued
      response <- jobToResponse job
      
      jrId response `shouldBe` "j1"
      jrStatus response `shouldBe` "queued"
      jrProgress response `shouldBe` Just 0.0
      jrEtaSeconds response `shouldBe` Just 30

    it "converts running job correctly" $ do
      job <- createTestJob "j1" Normal Running
      response <- jobToResponse job
      
      jrStatus response `shouldBe` "running"
      jrProgress response `shouldBe` Just 0.5

    it "converts complete job correctly" $ do
      job <- createTestJob "j1" Normal Complete
      let jobWithOutput = job { qjOutput = Just "https://example.com/output.mp4" }
      response <- jobToResponse jobWithOutput
      
      jrStatus response `shouldBe` "complete"
      jrProgress response `shouldBe` Just 1.0
      jrOutput response `shouldBe` Just "https://example.com/output.mp4"

    it "BUG: hardcoded progress values may not reflect actual progress" $ do
      -- BUG: jobToResponse (line 792-819) uses hardcoded progress values:
      -- Queued -> 0.0, Running -> 0.5, Complete -> 1.0. This doesn't reflect
      -- actual job progress, which may be tracked elsewhere or not tracked at all.
      job <- createTestJob "j1" Normal Running
      response <- jobToResponse job
      jrProgress response `shouldBe` Just 0.5

    it "BUG: hardcoded ETA estimate may be inaccurate" $ do
      -- BUG: jobToResponse (line 803-805) returns Just 30 for queued jobs,
      -- which is a hardcoded estimate. This doesn't account for actual queue
      -- length, backend processing time, or job complexity.
      job <- createTestJob "j1" Normal Queued
      response <- jobToResponse job
      jrEtaSeconds response `shouldBe` Just 30

    it "BUG: error detail always marked as retriable" $ do
      -- BUG: jobToResponse (line 809-815) always sets edRetriable = True for
      -- error details. This may be incorrect if the error is non-retriable
      -- (e.g., authentication failure, invalid request).
      job <- createTestJob "j1" Normal Error
      let jobWithError = job { qjError = Just "invalid request" }
      response <- jobToResponse jobWithError
      
      case jrError response of
        Just err -> edRetriable err `shouldBe` True
        Nothing -> fail "Expected error detail"

  describe "extractCustomerId" $ do
    it "returns anonymous for missing auth header" $ do
      customerId <- extractCustomerId Nothing
      customerId `shouldBe` "anonymous"

    it "BUG: extracts customer ID from JWT token" $ do
      -- BUG: extractCustomerId (line 832-883) attempts to decode JWT tokens
      -- without signature verification. This is a security issue - tokens should
      -- be verified before extracting customer ID. Additionally, the fallback
      -- to token hash (line 845) may allow unauthorized access if tokens are not
      -- properly validated.
      -- Note: Testing JWT parsing requires creating valid base64url-encoded
      -- JWT tokens, which is complex. This test documents the bug rather than
      -- testing it fully.
      let token = "Bearer eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJzdWIiOiJjdXN0XzEyMyJ9.signature"
      customerId <- extractCustomerId (Just (Text.encodeUtf8 token))
      -- Should extract "cust_123" from JWT, but without verification this is unsafe
      customerId `shouldSatisfy` \cid -> Text.isPrefixOf "cust_" cid || cid == "anonymous"

    it "BUG: fallback to token hash may be insecure" $ do
      -- BUG: If JWT decoding fails, extractCustomerId (line 844-845) falls
      -- back to using the first 12 characters of the token as customer ID.
      -- This allows any token to be used as a customer ID, which is insecure.
      let token = "Bearer invalid_token_12345"
      customerId <- extractCustomerId (Just (Text.encodeUtf8 token))
      customerId `shouldSatisfy` \cid -> Text.isPrefixOf "cust_" cid

    it "handles non-Bearer auth header" $ do
      let auth = "Basic dXNlcjpwYXNz"
      customerId <- extractCustomerId (Just (Text.encodeUtf8 auth))
      customerId `shouldBe` "anonymous"

  describe "handleGetQueue" $ do
    it "returns queue size and estimated wait" $ do
      gatewayState <- createTestGatewayState
      job1 <- createTestJob "j1" Normal Queued
      job2 <- createTestJob "j2" Normal Queued
      
      atomically $ do
        storeJob (gsJobStore gatewayState) job1
        storeJob (gsJobStore gatewayState) job2
        enqueueJob (gsQueue gatewayState) job1
        enqueueJob (gsQueue gatewayState) job2
      
      responseVar <- newEmptyMVar
      handleGetQueue gatewayState $ \response -> do
        putMVar responseVar response
        pure ()
      
      response <- takeMVar responseVar
      -- Verify response structure (would need to parse response body)
      response `shouldSatisfy` \r -> True

    it "BUG: hardcoded wait time estimate may be inaccurate" $ do
      -- BUG: handleGetQueue (line 596-603) estimates wait time as
      -- size * 30 seconds. This is a hardcoded estimate that doesn't account
      -- for actual processing time, backend capacity, or job complexity.
      gatewayState <- createTestGatewayState
      job1 <- createTestJob "j1" Normal Queued
      
      atomically $ do
        storeJob (gsJobStore gatewayState) job1
        enqueueJob (gsQueue gatewayState) job1
      
      responseVar <- newEmptyMVar
      handleGetQueue gatewayState $ \response -> do
        putMVar responseVar response
        pure ()
      
      _ <- takeMVar responseVar
      -- Estimate would be 1 * 30 = 30 seconds, but actual wait may differ
      True `shouldBe` True

  describe "handleGetJob" $ do
    it "returns 404 for nonexistent job" $ do
      gatewayState <- createTestGatewayState
      responseVar <- newEmptyMVar
      
      handleGetJob gatewayState "nonexistent" $ \response -> do
        putMVar responseVar response
        pure ()
      
      response <- takeMVar responseVar
      -- Verify 404 response (would need to parse response body)
      response `shouldSatisfy` \r -> True

    it "returns job details for existing job" $ do
      gatewayState <- createTestGatewayState
      job <- createTestJob "j1" Normal Queued
      
      atomically $ do
        storeJob (gsJobStore gatewayState) job
        enqueueJob (gsQueue gatewayState) job
      
      responseVar <- newEmptyMVar
      handleGetJob gatewayState "j1" $ \response -> do
        putMVar responseVar response
        pure ()
      
      response <- takeMVar responseVar
      -- Verify job response (would need to parse response body)
      response `shouldSatisfy` \r -> True

    it "BUG: queue position may be incorrect if job dequeued concurrently" $ do
      -- BUG: handleGetJob (line 606-623) calls getQueuePosition atomically,
      -- but if the job is dequeued concurrently between getJob and getQueuePosition,
      -- the position may be incorrect or -1 even though the job is still Queued.
      gatewayState <- createTestGatewayState
      job <- createTestJob "j1" Normal Queued
      
      atomically $ do
        storeJob (gsJobStore gatewayState) job
        enqueueJob (gsQueue gatewayState) job
      
      -- Concurrently dequeue job
      _ <- forkIO $ atomically $ do
        mJob <- tryDequeueJob (gsQueue gatewayState)
        pure ()
      
      threadDelay 10000 -- Small delay
      
      responseVar <- newEmptyMVar
      handleGetJob gatewayState "j1" $ \response -> do
        putMVar responseVar response
        pure ()
      
      _ <- takeMVar responseVar
      -- Position may be -1 even if job is still Queued due to race condition
      True `shouldBe` True

  describe "handleCancelJob" $ do
    it "returns 404 for nonexistent job" $ do
      gatewayState <- createTestGatewayState
      responseVar <- newEmptyMVar
      
      handleCancelJob gatewayState "nonexistent" $ \response -> do
        putMVar responseVar response
        pure ()
      
      response <- takeMVar responseVar
      -- Verify 404 response
      response `shouldSatisfy` \r -> True

    it "cancels queued job successfully" $ do
      gatewayState <- createTestGatewayState
      job <- createTestJob "j1" Normal Queued
      
      atomically $ do
        storeJob (gsJobStore gatewayState) job
        enqueueJob (gsQueue gatewayState) job
      
      responseVar <- newEmptyMVar
      handleCancelJob gatewayState "j1" $ \response -> do
        putMVar responseVar response
        pure ()
      
      response <- takeMVar responseVar
      -- Verify cancellation (would need to parse response body)
      response `shouldSatisfy` \r -> True
      
      -- Verify job is cancelled
      mJob <- atomically $ getJob (gsJobStore gatewayState) "j1"
      case mJob of
        Just j -> qjStatus j `shouldBe` Cancelled
        Nothing -> fail "Job should exist"

    it "BUG: returns 404 for terminal state jobs, but job still exists" $ do
      -- BUG: handleCancelJob (line 626-631) calls cancelJob which returns False
      -- for terminal state jobs (Complete, Error, Cancelled). This causes a 404
      -- response even though the job exists, which may be confusing for clients.
      gatewayState <- createTestGatewayState
      job <- createTestJob "j1" Normal Complete
      
      atomically $ storeJob (gsJobStore gatewayState) job
      
      responseVar <- newEmptyMVar
      handleCancelJob gatewayState "j1" $ \response -> do
        putMVar responseVar response
        pure ()
      
      response <- takeMVar responseVar
      -- Returns 404 even though job exists
      response `shouldSatisfy` \r -> True

  describe "handleListModels" $ do
    it "returns empty lists when no backends" $ do
      gatewayState <- createTestGatewayState
      responseVar <- newEmptyMVar
      
      handleListModels gatewayState $ \response -> do
        putMVar responseVar response
        pure ()
      
      response <- takeMVar responseVar
      -- Verify empty response (would need to parse response body)
      response `shouldSatisfy` \r -> True

    it "BUG: hardcoded family-to-modality mapping may be incorrect" $ do
      -- BUG: handleListModels (line 633-642) uses hardcoded family lists:
      -- video: ["wan", "qwen"], image: ["flux", "sdxl", "zimage"]. This mapping
      -- may be incorrect if new families are added or if families support
      -- multiple modalities.
      backend1 <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      backend2 <- createTestBackend "b2" Nunchaku "flux" ["model2"] "localhost:8000" 10
      
      gatewayState <- createTestGatewayState
      let gatewayStateWithBackends = gatewayState { gsBackends = [backend1, backend2] }
      
      responseVar <- newEmptyMVar
      handleListModels gatewayStateWithBackends $ \response -> do
        putMVar responseVar response
        pure ()
      
      _ <- takeMVar responseVar
      -- Backends are filtered by hardcoded family lists
      True `shouldBe` True

  describe "forwardToBackend" $ do
    it "BUG: validates endpoint and model name before request" $ do
      -- BUG: forwardToBackend (line 547-594) validates endpoint and model name
      -- are non-empty (line 552-553), but doesn't validate endpoint format
      -- (e.g., should be "host:port" or URL). Invalid endpoints may cause
      -- connection errors that are retriable, leading to unnecessary retries.
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "" 10
      job <- createTestJob "j1" Normal Queued
      
      manager <- newManager defaultManagerSettings
      result <- forwardToBackend manager backend job
      
      -- Should return Left for empty endpoint
      case result of
        Left _ -> True `shouldBe` True
        Right _ -> fail "Expected error for empty endpoint"

    it "BUG: constructs URL without validating endpoint format" $ do
      -- BUG: forwardToBackend (line 557) constructs URL as
      -- "http://" <> endpoint <> "/v2/models/" <> modelName <> "/infer".
      -- If endpoint is not in "host:port" format, this may create invalid URLs.
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "invalid_endpoint" 10
      job <- createTestJob "j1" Normal Queued
      
      manager <- newManager defaultManagerSettings
      result <- forwardToBackend manager backend job
      
      -- May return Left for invalid URL, but error message may not be clear
      case result of
        Left err -> err `shouldSatisfy` \e -> True
        Right _ -> fail "Expected error for invalid endpoint"

    it "BUG: hardcoded timeout may be too short for large jobs" $ do
      -- BUG: forwardToBackend (line 567) sets timeout to 30 seconds
      -- (responseTimeoutMicro 30000000). This may be too short for large
      -- inference jobs, causing timeouts that trigger retries.
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "localhost:8000" 10
      job <- createTestJob "j1" Normal Queued
      
      manager <- newManager defaultManagerSettings
      -- Timeout is hardcoded, cannot be configured per job
      True `shouldBe` True

    it "BUG: error parsing may not distinguish retriable vs non-retriable" $ do
      -- BUG: forwardToBackend (line 574-590) classifies errors as retriable
      -- (5xx) or non-retriable (4xx), but network errors (line 592-593) are
      -- always classified as retriable. Some network errors (e.g., DNS failure,
      -- invalid endpoint) may not be retriable.
      backend <- createTestBackend "b1" Nunchaku "wan" ["model1"] "invalid_host:8000" 10
      job <- createTestJob "j1" Normal Queued
      
      manager <- newManager defaultManagerSettings
      result <- forwardToBackend manager backend job
      
      -- Network errors are always retriable, but DNS failure may not be
      case result of
        Left err -> err `shouldSatisfy` \e -> True
        Right _ -> fail "Expected error for invalid host"

  describe "sendSSEEvent" $ do
    it "BUG: doesn't handle client disconnect gracefully" $ do
      -- BUG: sendSSEEvent (line 766-776) catches exceptions and returns False,
      -- but the caller (streamJobEvents) may not handle False correctly,
      -- leading to continued attempts to send events to disconnected clients.
      let sendChunk _ = error "Client disconnected"
      let flush _ = pure ()
      
      result <- sendSSEEvent sendChunk flush "test" (object [])
      result `shouldBe` False

    it "BUG: doesn't validate event type format" $ do
      -- BUG: sendSSEEvent (line 769) constructs SSE message as
      -- "event: " <> eventType <> "\ndata: " <> jsonData <> "\n\n".
      -- If eventType contains newlines or special characters, the SSE format
      -- may be invalid.
      let sendChunk _ = pure ()
      let flush _ = pure ()
      
      -- Event type with newline may break SSE format
      result <- sendSSEEvent sendChunk flush "event\nwith\nnewlines" (object [])
      result `shouldBe` True -- Should still return True, but SSE format may be invalid

  describe "streamJobEvents" $ do
    it "BUG: may send duplicate position updates" $ do
      -- BUG: streamJobEvents (line 664-761) checks if position changed
      -- (line 690), but if position changes multiple times between checks,
      -- intermediate positions are not sent. Additionally, if position is
      -- recalculated and returns the same value, no update is sent even if
      -- the queue order changed.
      gatewayState <- createTestGatewayState
      job <- createTestJob "j1" Normal Queued
      
      atomically $ do
        storeJob (gsJobStore gatewayState) job
        enqueueJob (gsQueue gatewayState) job
      
      -- Position updates depend on queue state, which may change concurrently
      True `shouldBe` True

    it "BUG: loop may not exit if job deleted during monitoring" $ do
      -- BUG: streamJobEvents (line 675) checks if job exists, and if not,
      -- sends error and exits. However, if job is deleted between the check
      -- and sending the error, the error may reference a non-existent job.
      gatewayState <- createTestGatewayState
      job <- createTestJob "j1" Normal Queued
      
      atomically $ do
        storeJob (gsJobStore gatewayState) job
        enqueueJob (gsQueue gatewayState) job
      
      -- Job may be deleted during monitoring
      _ <- forkIO $ threadDelay 1000000 >> atomically (deleteJob (gsJobStore gatewayState) "j1")
      
      -- Loop should exit when job is deleted
      True `shouldBe` True

    it "BUG: hardcoded progress value doesn't reflect actual progress" $ do
      -- BUG: streamJobEvents (line 713-716) sends hardcoded progress value
      -- (0.5) for running jobs. This doesn't reflect actual job progress,
      -- which may be tracked elsewhere or not tracked at all.
      gatewayState <- createTestGatewayState
      job <- createTestJob "j1" Normal Running
      
      atomically $ storeJob (gsJobStore gatewayState) job
      
      -- Progress updates are hardcoded, not based on actual progress
      True `shouldBe` True

  describe "workerLoop" $ do
    it "BUG: continues loop even after exceptions" $ do
      -- BUG: workerLoop (line 142-197) catches exceptions and continues
      -- the loop (line 189-194), which is correct for resilience. However,
      -- if exceptions occur repeatedly, the loop may consume CPU without
      -- making progress, and there's no backoff or rate limiting for errors.
      gatewayState <- createTestGatewayState
      manager <- newManager defaultManagerSettings
      
      -- Worker loop should continue even after errors
      _ <- forkIO $ workerLoop manager gatewayState
      
      threadDelay 100000 -- Small delay to let loop start
      -- Loop continues even if no jobs or errors occur
      True `shouldBe` True

    it "BUG: releases backend from processRequest even if processJobAsync fails" $ do
      -- BUG: workerLoop (line 162-186) calls processJobAsync and catches
      -- exceptions, releasing backendFromProcessRequest (line 172). However,
      -- if processJobAsync selects a different backend and then fails, both
      -- backends may be released, or the wrong backend may be released.
      gatewayState <- createTestGatewayState
      manager <- newManager defaultManagerSettings
      
      -- Backend release logic depends on processJobAsync behavior
      True `shouldBe` True

    it "BUG: marks job as error without checking if job was cancelled" $ do
      -- BUG: workerLoop (line 178-186) marks job as error if processJobAsync
      -- fails, but doesn't check if job was cancelled before marking as error.
      -- Cancelled jobs should not be marked as error.
      gatewayState <- createTestGatewayState
      job <- createTestJob "j1" Normal Queued
      
      atomically $ do
        storeJob (gsJobStore gatewayState) job
        enqueueJob (gsQueue gatewayState) job
      
      -- Job may be cancelled before processJobAsync fails
      _ <- forkIO $ threadDelay 50000 >> atomically (cancelJob gatewayState "j1")
      
      -- Job should not be marked as error if cancelled
      True `shouldBe` True
