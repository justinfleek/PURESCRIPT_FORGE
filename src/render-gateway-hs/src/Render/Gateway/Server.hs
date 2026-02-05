{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveGeneric #-}

-- | Render Gateway Warp HTTP Server
-- | HTTP endpoints for inference gateway per render.openapi.yaml
module Render.Gateway.Server where

import Prelude hiding (head, tail)
import Control.Concurrent.STM
import Control.Concurrent (forkIO, threadDelay)
import Control.Exception (try, SomeException)
import Control.Monad (unless)
import Data.Aeson (encode, decode, eitherDecode, Value(..), ToJSON(..), FromJSON(..), (.:), (.:?), (.=), object)
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.KeyMap as KM
import Data.Aeson.Key (fromText)
import Data.ByteString (ByteString)
import Data.ByteString.Lazy (LazyByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Network.Wai (Request, Response, requestMethod, pathInfo, rawQueryString, requestBody, responseLBS, requestHeaders, strictRequestBody, responseStream, StreamingBody)
import Network.Wai.Handler.Warp (run, Port)
import Network.HTTP.Types.Header (hCacheControl, hConnection)
import Network.HTTP.Types (status200, status201, status400, status404, status429, status500, status503, methodPost, methodGet, methodDelete, hContentType, hAuthorization, QueryText, parseQueryText)
import Network.HTTP.Client (Manager, newManager, defaultManagerSettings, httpLbs, parseRequest, Request(..), RequestBody(..), responseBody, responseStatus, responseTimeoutMicro)
import Network.HTTP.Types.Status (statusCode)
import Render.Gateway.Core (GatewayState(..), JobStore(..), processRequest, handleRequestSuccess, handleRequestFailure, storeJob, getJob, updateJob, cancelJob, getQueuePosition)
import Render.Gateway.STM.Queue (QueuedJob(..), Priority(..), JobStatus(..), Modality(..), TaskType(..), enqueueJob, queueSize, parseTaskType, parseModality, parsePriority, isEmpty)
import Render.Gateway.STM.Clock (readClockSTM)
import Render.Gateway.Backend (Backend(..), BackendType(..))
import qualified Render.Gateway.STM.RateLimiter
import qualified Render.Gateway.Backend
import qualified Data.Map.Strict as Map
import Data.Time (getCurrentTime, UTCTime)
import Data.UUID (UUID)
import Data.UUID.V4 (nextRandom)
import qualified Data.UUID as UUID
import GHC.Generics (Generic)
import qualified Data.ByteString.Base64.URL as Base64URL

-- | JSON response types per OpenAPI spec
data JobCreatedResponse = JobCreatedResponse
  { jcrId :: Text
  , jcrStatus :: Text
  , jcrPosition :: Int
  , jcrEtaSeconds :: Maybe Int
  , jcrEventsUrl :: Maybe Text
  } deriving (Generic)

instance ToJSON JobCreatedResponse where
  toJSON JobCreatedResponse {..} = object
    [ "id" .= jcrId
    , "status" .= jcrStatus
    , "position" .= jcrPosition
    , "eta_seconds" .= jcrEtaSeconds
    , "events_url" .= jcrEventsUrl
    ]

data JobResponse = JobResponse
  { jrId :: Text
  , jrStatus :: Text
  , jrPosition :: Maybe Int
  , jrProgress :: Maybe Double
  , jrEtaSeconds :: Maybe Int
  , jrOutput :: Maybe Text
  , jrOutputs :: Maybe [Text]
  , jrSeed :: Maybe Int
  , jrError :: Maybe ErrorDetail
  , jrCreatedAt :: Text
  , jrStartedAt :: Maybe Text
  , jrCompletedAt :: Maybe Text
  } deriving (Generic)

data ErrorDetail = ErrorDetail
  { edCode :: Text
  , edMessage :: Text
  , edRetriable :: Bool
  } deriving (Generic)

instance ToJSON ErrorDetail where
  toJSON ErrorDetail {..} = object
    [ "code" .= edCode
    , "message" .= edMessage
    , "retriable" .= edRetriable
    ]

instance ToJSON JobResponse where
  toJSON JobResponse {..} = object
    [ "id" .= jrId
    , "status" .= jrStatus
    , "position" .= jrPosition
    , "progress" .= jrProgress
    , "eta_seconds" .= jrEtaSeconds
    , "output" .= jrOutput
    , "outputs" .= jrOutputs
    , "seed" .= jrSeed
    , "error" .= jrError
    , "created_at" .= jrCreatedAt
    , "started_at" .= jrStartedAt
    , "completed_at" .= jrCompletedAt
    ]

data ErrorResponse = ErrorResponse
  { erError :: Text
  , erMessage :: Text
  , erRequestId :: Maybe Text
  } deriving (Generic)

instance ToJSON ErrorResponse where
  toJSON ErrorResponse {..} = object
    [ "error" .= erError
    , "message" .= erMessage
    , "request_id" .= erRequestId
    ]

-- | Start gateway HTTP server
startServer :: Port -> GatewayState -> IO ()
startServer port gatewayState = do
  putStrLn $ "Starting Render Gateway on port " <> show port
  putStrLn "Routes:"
  putStrLn "  POST /{modality}/{family}/{model}/{task}"
  putStrLn "  GET  /queue"
  putStrLn "  GET  /jobs/{job_id}"
  putStrLn "  GET  /jobs/{job_id}/events (SSE)"
  putStrLn "  POST /jobs/{job_id}/cancel"
  putStrLn "  GET  /models"
  manager <- newManager defaultManagerSettings
  
  -- Start worker loop to continuously process queued jobs
  _workerThread <- forkIO $ workerLoop manager gatewayState
  
  run port (app manager gatewayState)

-- | Worker loop that continuously processes queued jobs
-- | Handles jobs that were requeued due to no backend availability or retries
-- | Includes error handling to prevent worker loop from crashing on exceptions
workerLoop :: Manager -> GatewayState -> IO ()
workerLoop manager gatewayState = do
  result <- try $ do
    -- Check for queued jobs
    mResult <- atomically $ do
      isEmpty <- Render.Gateway.STM.Queue.isEmpty (gsQueue gatewayState)
      if isEmpty
        then pure Nothing
        else processRequest gatewayState
    
    case mResult of
      Nothing -> do
        -- No jobs to process, wait before checking again
        threadDelay 1000000 -- 1 second
      Just (job, backendFromProcessRequest) -> do
        -- Process the job asynchronously with error handling
        -- Note: processRequest already selected a backend and marked job as Running
        -- processJobAsync will select its own backend (potentially different one)
        -- We must release backendFromProcessRequest when processJobAsync selects its own backend
        -- to prevent counter leak
        processResult <- try $ processJobAsync manager gatewayState job (Just backendFromProcessRequest)
        case processResult of
          Left (e :: SomeException) -> do
            -- Log error and mark job as failed
            -- Job was already dequeued by processRequest, so we must handle it
            -- Backend from processRequest was selected but processJobAsync failed before selecting its own
            -- Release backendFromProcessRequest to prevent leak
            putStrLn $ "Error processing job " <> Text.unpack (qjJobId job) <> ": " <> show e
            atomically $ do
              -- Release backend from processRequest (it was selected but processJobAsync failed)
              Render.Gateway.Backend.releaseBackend backendFromProcessRequest
              -- Mark job as failed
              mCurrentJob <- getJob (gsJobStore gatewayState) (qjJobId job)
              case mCurrentJob of
                Nothing -> pure () -- Job was deleted, ignore
                Just currentJob ->
                  if qjStatus currentJob == Cancelled
                    then pure () -- Job was cancelled, ignore
                    else do
                      -- Mark as error - job processing failed
                      _ <- updateJob (gsJobStore gatewayState) (qjJobId job) (\j -> j
                        { qjStatus = Error
                        , qjError = Just $ "Failed to process job: " <> Text.pack (show e)
                        })
                      pure ()
  
  -- Continue loop regardless of errors (worker loop must be resilient)
  case result of
    Left (e :: SomeException) -> do
      -- Log error and continue (worker loop must never crash)
      putStrLn $ "Worker loop error (continuing): " <> show e
      threadDelay 1000000 -- Wait before retrying
    Right _ -> pure ()
  
  -- Continue processing
  workerLoop manager gatewayState

-- | WAI application with routing per OpenAPI spec
app :: Manager -> GatewayState -> Request -> (Response -> IO t) -> IO t
app manager gatewayState req respond =
  case (requestMethod req, pathInfo req) of
    -- POST /{modality}/{family}/{model}/{task} - Generate content
    (method, [modality, family, model, task]) | method == methodPost ->
      handleGenerate manager gatewayState modality family model task req respond

    -- GET /queue - Get queue status
    (method, ["queue"]) | method == methodGet ->
      handleGetQueue gatewayState respond

    -- GET /jobs/{job_id} - Get job status
    (method, ["jobs", jobId]) | method == methodGet ->
      handleGetJob gatewayState jobId respond

    -- GET /jobs/{job_id}/events - Subscribe to job events (SSE)
    (method, ["jobs", jobId, "events"]) | method == methodGet ->
      handleJobEvents gatewayState jobId respond

    -- POST /jobs/{job_id}/cancel - Cancel job
    (method, ["jobs", jobId, "cancel"]) | method == methodPost ->
      handleCancelJob gatewayState jobId respond

    -- DELETE /jobs/{job_id} - Delete job (alias for cancel)
    (method, ["jobs", jobId]) | method == methodDelete ->
      handleCancelJob gatewayState jobId respond

    -- GET /models - List available models
    (method, ["models"]) | method == methodGet ->
      handleListModels gatewayState respond

    -- Health check
    (method, ["health"]) | method == methodGet ->
      respond (jsonResponse 200 (object ["status" .= ("ok" :: Text)]))

    -- Not found
    _ ->
      respond (errorResponse 404 "not_found" "Route not found" Nothing)

-- | Handle content generation request
-- | Route: POST /{modality}/{family}/{model}/{task}
handleGenerate :: Manager -> GatewayState -> Text -> Text -> Text -> Text -> Request -> (Response -> IO t) -> IO t
handleGenerate manager gatewayState modalityText family model taskText req respond = do
  -- Validate non-empty path parameters
  if Text.null modalityText || Text.null family || Text.null model || Text.null taskText
    then respond (errorResponse 400 "invalid_parameters" "Modality, family, model, and task must be non-empty" Nothing)
    else do
      -- Parse modality
      case parseModality modalityText of
        Nothing -> respond (errorResponse 400 "invalid_modality" ("Invalid modality: " <> modalityText) Nothing)
        Just modality -> do
          -- Parse task
          case parseTaskType taskText of
            Nothing -> respond (errorResponse 400 "invalid_task" ("Invalid task: " <> taskText) Nothing)
            Just task -> do
          -- Parse query parameters
          let queryParams = parseQueryText (rawQueryString req)
          let mFormat = lookupQuery "format" queryParams
          let mBackend = lookupQuery "backend" queryParams
          let mPriority = lookupQuery "priority" queryParams

          -- Parse request body with size limit (10MB max) and error handling
          bodyResult <- try $ strictRequestBody req
          case bodyResult of
            Left (e :: SomeException) -> respond (errorResponse 400 "request_read_error" ("Failed to read request body: " <> Text.pack (show e)) Nothing)
            Right body -> do
              let bodySize = LBS.length body
              if bodySize > 10 * 1024 * 1024 -- 10MB limit
                then respond (errorResponse 413 "request_too_large" ("Request body exceeds 10MB limit (got " <> Text.pack (show bodySize) <> " bytes)") Nothing)
                else if bodySize == 0
                  then respond (errorResponse 400 "empty_body" "Request body cannot be empty" Nothing)
                  else case eitherDecode body of
                    Left err -> respond (errorResponse 400 "invalid_json" (Text.pack err) Nothing)
                    Right requestValue -> do
                      -- Extract customer ID from auth header
                      let authHeader = lookup hAuthorization (requestHeaders req)
                      customerId <- extractCustomerId authHeader

                      -- Generate IDs (UUID generation is total, but wrap in try for safety)
                      uuidResult <- try $ do
                        jobUuid <- nextRandom
                        reqUuid <- nextRandom
                        pure (jobUuid, reqUuid)
                      
                      case uuidResult of
                        Left (e :: SomeException) -> respond (errorResponse 500 "internal_error" ("Failed to generate job ID: " <> Text.pack (show e)) Nothing)
                        Right (jobUuid, reqUuid) -> do
                          let jobId = "j_" <> Text.pack (filter (/= '-') (UUID.toString jobUuid))
                          let requestId = "req_" <> Text.pack (filter (/= '-') (UUID.toString reqUuid))

                          -- Get current time
                          now <- getCurrentTime

                          -- Create job
                          let job = QueuedJob
                                { qjJobId = jobId
                                , qjRequestId = requestId
                                , qjCustomerId = customerId
                                , qjModality = modality
                                , qjModelFamily = family
                                , qjModelName = model
                                , qjTask = task
                                , qjFormat = mFormat
                                , qjBackend = mBackend
                                , qjPriority = maybe Normal parsePriority mPriority
                                , qjStatus = Queued
                                , qjCreatedAt = now
                                , qjStartedAt = Nothing
                                , qjCompletedAt = Nothing
                                , qjRequest = requestValue
                                , qjOutput = Nothing
                                , qjError = Nothing
                                , qjRetryCount = 0
                                }

                          -- Store and enqueue job
                          position <- atomically $ do
                            storeJob (gsJobStore gatewayState) job
                            enqueueJob (gsQueue gatewayState) job
                            queueSize (gsQueue gatewayState)

                          -- Start async processing with error handling
                          -- Note: Job is Queued, no backend selected yet (processJobAsync will select one)
                          _ <- forkIO $ do
                            processResult <- try $ processJobAsync manager gatewayState job Nothing
                            case processResult of
                              Left (e :: SomeException) -> do
                                -- Log error and mark job as failed if processing fails immediately
                                atomically $ do
                                  _ <- updateJob (gsJobStore gatewayState) jobId (\j -> j
                                    { qjStatus = Error
                                    , qjError = Just $ "Failed to start processing: " <> Text.pack (show e)
                                    })
                                  pure ()
                              Right _ -> pure ()

                          -- Return job created response
                          let response = JobCreatedResponse
                                { jcrId = jobId
                                , jcrStatus = "queued"
                                , jcrPosition = fromIntegral position
                                , jcrEtaSeconds = Just (fromIntegral position * 30) -- Estimate 30s per job
                                , jcrEventsUrl = Just $ "/jobs/" <> jobId <> "/events"
                                }
                          respond (jsonResponseWithHeaders 201
                            [ ("X-Request-Id", Text.encodeUtf8 requestId)
                            , ("Location", Text.encodeUtf8 $ "/jobs/" <> jobId)
                            ] (toJSON response))

-- | Process a specific job asynchronously
-- | Handles rate limiting, backend selection, forwarding, and retries
-- | mBackendFromProcessRequest: Backend selected by processRequest (if any, must be released if we select different one)
-- |   - Just backend: Called from workerLoop via processRequest (job already Running)
-- |   - Nothing: Called directly from handleGenerate (job is Queued, will be marked Running)
processJobAsync :: Manager -> GatewayState -> QueuedJob -> Maybe Backend -> IO ()
processJobAsync manager gatewayState job mBackendFromProcessRequest = do
  -- Check rate limiting and select backend for this specific job
  result <- atomically $ do
    -- Get or create rate limiter for customer
    limiters <- readTVar (gsRateLimiters gatewayState)
    let customerId = qjCustomerId job
    rateLimiter <- case Map.lookup customerId limiters of
      Just rl -> pure rl
      Nothing -> do
        -- Create default rate limiter (100 req/s, 1000 capacity)
        (_, now) <- readClockSTM (gsClock gatewayState)
        rl <- Render.Gateway.STM.RateLimiter.createRateLimiter 1000.0 100.0 now
        modifyTVar' (gsRateLimiters gatewayState) (Map.insert customerId rl)
        pure rl

    -- Acquire rate limit token (blocking with retry)
    Render.Gateway.STM.RateLimiter.acquireTokenBlocking rateLimiter (gsClock gatewayState)

    -- Select backend for this job (may be different from backendFromProcessRequest)
    backend <- Render.Gateway.Backend.selectBackend (gsBackends gatewayState) (qjModelFamily job) (qjModelName job) (qjBackend job) (gsClock gatewayState)

    case backend of
      Nothing -> do
        -- No backend available, release backendFromProcessRequest if provided
        case mBackendFromProcessRequest of
          Just backendFromProcessRequest -> Render.Gateway.Backend.releaseBackend backendFromProcessRequest
          Nothing -> pure ()
        pure Nothing
      Just b -> do
        -- If we have a backend from processRequest and selected a different one, release it
        -- to prevent counter leak
        case mBackendFromProcessRequest of
          Just backendFromProcessRequest ->
            if beId b /= beId backendFromProcessRequest
              then Render.Gateway.Backend.releaseBackend backendFromProcessRequest
              else pure ()
          Nothing -> pure ()
        
        -- Update job status to Running if not already Running (called from handleGenerate)
        -- If already Running (called from workerLoop), just verify job exists
        mCurrentJob <- getJob (gsJobStore gatewayState) (qjJobId job)
        case mCurrentJob of
          Nothing -> do
            -- Job was deleted, release backend
            Render.Gateway.Backend.releaseBackend b
            pure Nothing
          Just currentJob ->
            if qjStatus currentJob == Cancelled
              then do
                -- Job was cancelled, release backend
                Render.Gateway.Backend.releaseBackend b
                pure Nothing
              else do
                -- If job is Queued (called from handleGenerate), mark as Running
                -- If already Running (called from workerLoop), no update needed
                if qjStatus currentJob == Queued
                  then do
                    (_, now) <- readClockSTM (gsClock gatewayState)
                    updated <- updateJob (gsJobStore gatewayState) (qjJobId job) (\j -> j
                      { qjStatus = Running
                      , qjStartedAt = Just now
                      })
                    if updated
                      then pure (Just b)
                      else do
                        Render.Gateway.Backend.releaseBackend b
                        pure Nothing
                  else pure (Just b)

  case result of
    Nothing -> do
      -- No backend available, requeue job (job was already dequeued)
      -- Check if job was cancelled before requeueing
      mCurrentJob <- atomically $ getJob (gsJobStore gatewayState) (qjJobId job)
      case mCurrentJob of
        Nothing -> pure () -- Job was deleted, don't requeue
        Just currentJob -> 
          if qjStatus currentJob == Cancelled
            then pure () -- Job was cancelled, don't requeue
            else atomically $ do
              -- Requeue job with current state (may have been updated)
              enqueueJob (gsQueue gatewayState) currentJob
    Just backend -> do
      -- Check if job was cancelled before forwarding
      currentJob <- atomically $ getJob (gsJobStore gatewayState) (qjJobId job)
      case currentJob of
        Nothing -> do
          -- Job was deleted, release backend (decrement in-flight counter)
          atomically $ Render.Gateway.Backend.releaseBackend backend
          pure ()
        Just j -> if qjStatus j == Cancelled
          then do
            -- Job was cancelled, release backend (decrement in-flight counter)
            atomically $ Render.Gateway.Backend.releaseBackend backend
            pure ()
          else do
            -- Forward to backend
            forwardResult <- forwardToBackend manager backend job
            case forwardResult of
              Left err -> do
                -- Check if job was cancelled during request
                cancelledCheck <- atomically $ do
                  mCurrentJob <- getJob (gsJobStore gatewayState) (qjJobId job)
                  case mCurrentJob of
                    Nothing -> pure True -- Job deleted
                    Just currentJob -> pure (qjStatus currentJob == Cancelled)
                
                if cancelledCheck
                  then do
                    -- Job was cancelled, release backend (decrement in-flight counter)
                    atomically $ Render.Gateway.Backend.releaseBackend backend
                    pure ()
                  else do
                    -- Check if error is retriable
                    let isRetriable = isRetriableError err
                    let maxRetries = 3
                    
                    if isRetriable && qjRetryCount job < maxRetries then do
                      -- Retry: requeue job with incremented retry count
                      -- Update job with incremented retry count and requeue
                      mRetriedJob <- atomically $ do
                        updated <- updateJob (gsJobStore gatewayState) (qjJobId job) (\j -> j
                          { qjRetryCount = qjRetryCount j + 1
                          , qjStatus = Queued
                          })
                        if updated
                          then do
                            -- Get updated job and requeue (only if not cancelled)
                            mUpdatedJob <- getJob (gsJobStore gatewayState) (qjJobId job)
                            case mUpdatedJob of
                              Just updatedJob -> 
                                if qjStatus updatedJob == Cancelled
                                  then pure Nothing -- Job was cancelled, don't requeue
                                  else do
                                    enqueueJob (gsQueue gatewayState) updatedJob
                                    pure (Just updatedJob)
                              Nothing -> pure Nothing -- Job was deleted, skip requeue
                          else pure Nothing -- Job doesn't exist, skip requeue
                      case mRetriedJob of
                        Nothing -> pure () -- Job was deleted or doesn't exist, skip retry
                        Just retriedJob -> do
                          -- Check if job was cancelled before retrying
                          cancelledCheck <- atomically $ do
                            mCurrentJob <- getJob (gsJobStore gatewayState) (qjJobId job)
                            case mCurrentJob of
                              Nothing -> pure True -- Job deleted
                              Just currentJob -> pure (qjStatus currentJob == Cancelled)
                          
                          if cancelledCheck
                            then pure () -- Job was cancelled, don't retry
                            else do
                              -- Retry after exponential backoff delay
                              -- Use retriedJob's retry count (already incremented)
                              let delaySeconds = 2 ^ (qjRetryCount retriedJob) -- 1s, 2s, 4s
                              threadDelay (delaySeconds * 1000000) -- Convert to microseconds
                              -- Retry processing with updated job
                              -- Note: For retries, we don't have backendFromProcessRequest (job was requeued)
                              -- processJobAsync will select its own backend
                              processJobAsync manager gatewayState retriedJob Nothing
                    else do
                      -- Non-retriable or max retries exceeded: mark as failed
                      atomically $ handleRequestFailure gatewayState job backend err
              Right outputUrl -> do
                -- Check if job was cancelled before marking as success
                cancelledCheck <- atomically $ do
                  mCurrentJob <- getJob (gsJobStore gatewayState) (qjJobId job)
                  case mCurrentJob of
                    Nothing -> pure True -- Job deleted
                    Just currentJob -> pure (qjStatus currentJob == Cancelled)
                
                if cancelledCheck
                  then do
                    -- Job was cancelled, release backend (decrement in-flight counter)
                    -- Note: handleRequestSuccess/handleRequestFailure will also release, but
                    -- we need to release here since we're not calling them
                    atomically $ Render.Gateway.Backend.releaseBackend backend
                    pure ()
                  else atomically $ handleRequestSuccess gatewayState job backend outputUrl

-- | Check if error is retriable (network errors, timeouts, 5xx status codes)
isRetriableError :: Text -> Bool
isRetriableError errText =
  let errLower = Text.toLower errText
  in Text.isInfixOf "timeout" errLower ||
     Text.isInfixOf "connection" errLower ||
     Text.isInfixOf "network" errLower ||
     Text.isInfixOf "status 5" errLower ||
     Text.isInfixOf "status 503" errLower ||
     Text.isInfixOf "status 502" errLower ||
     Text.isInfixOf "status 504" errLower

-- | Forward request to inference backend
forwardToBackend :: Manager -> Backend -> QueuedJob -> IO (Either Text Text)
forwardToBackend manager backend job = do
  -- Validate endpoint and model name are non-empty before attempting request
  let endpoint = Text.unpack (beEndpoint backend)
  let modelName = Text.unpack (qjModelName job)
  if null endpoint || null modelName
    then pure (Left "Invalid backend endpoint or model name")
    else do
      result <- try $ do
        -- Build request to backend
        let url = "http://" <> endpoint <> "/v2/models/" <> modelName <> "/infer"
        
        initialRequest <- parseRequest url
        let request = initialRequest
              { method = "POST"
              , requestBody = RequestBodyLBS (encode (qjRequest job))
              , requestHeaders =
                  [ ("Content-Type", "application/json")
                  , ("X-Request-Id", Text.encodeUtf8 (qjRequestId job))
                  ]
              , responseTimeout = responseTimeoutMicro 30000000 -- 30 second timeout
              }

        -- Send request with timeout
        response <- httpLbs request manager

        -- Check response
        case statusCode (responseStatus response) of
          200 -> do
            -- Parse output URL from response
            case eitherDecode (responseBody response) of
              Left _ -> pure (Left "Failed to parse backend response")
              Right (Object obj) -> do
                case KM.lookup "output" obj of
                  Just (String outputUrl) -> pure (Right outputUrl)
                  _ -> pure (Right $ "https://cdn.render.weyl.ai/outputs/" <> qjJobId job <> ".mp4")
              _ -> pure (Right $ "https://cdn.render.weyl.ai/outputs/" <> qjJobId job <> ".mp4")
          -- 5xx errors are retriable
          500 -> pure (Left "Backend returned status 500 (retriable)")
          502 -> pure (Left "Backend returned status 502 (retriable)")
          503 -> pure (Left "Backend returned status 503 (retriable)")
          504 -> pure (Left "Backend returned status 504 (retriable)")
          -- 4xx errors are not retriable (client errors)
          code -> pure (Left $ "Backend returned status " <> Text.pack (show code) <> " (non-retriable)")

      case result of
        Left (e :: SomeException) -> pure (Left $ "Backend error: " <> Text.pack (show e))
        Right r -> pure r

-- | Handle get queue status
handleGetQueue :: GatewayState -> (Response -> IO t) -> IO t
handleGetQueue gatewayState respond = do
  size <- atomically $ queueSize (gsQueue gatewayState)
  respond (jsonResponse 200 (object
    [ "queue_length" .= size
    , "estimated_wait_seconds" .= (size * 30)
    ]))

-- | Handle get job status
handleGetJob :: GatewayState -> Text -> (Response -> IO t) -> IO t
handleGetJob gatewayState jobId respond = do
  mJob <- atomically $ getJob (gsJobStore gatewayState) jobId
  case mJob of
    Nothing -> respond (errorResponse 404 "job_not_found" ("Job not found: " <> jobId) Nothing)
    Just job -> do
      -- Get queue position if job is queued
      position <- atomically $ case qjStatus job of
        Queued -> getQueuePosition (gsQueue gatewayState) jobId
        _ -> pure (-1)
      
      -- Build response with position if queued
      let baseResponse = jobToResponse job
      let response = if position >= 0
            then baseResponse { jrPosition = Just position }
            else baseResponse
      
      respond (jsonResponse 200 (toJSON response))

-- | Handle cancel job
handleCancelJob :: GatewayState -> Text -> (Response -> IO t) -> IO t
handleCancelJob gatewayState jobId respond = do
  success <- atomically $ cancelJob gatewayState jobId
  if success
    then respond (jsonResponse 200 (object ["cancelled" .= True, "id" .= jobId]))
    else respond (errorResponse 404 "job_not_found" ("Job not found or cannot be cancelled: " <> jobId) Nothing)

-- | Handle list models
handleListModels :: GatewayState -> (Response -> IO t) -> IO t
handleListModels gatewayState respond = do
  let backends = gsBackends gatewayState
  let videoModels = concatMap backendToModels (filter (\b -> beFamily b `elem` ["wan", "qwen"]) backends)
  let imageModels = concatMap backendToModels (filter (\b -> beFamily b `elem` ["flux", "sdxl", "zimage"]) backends)
  respond (jsonResponse 200 (object
    [ "video" .= videoModels
    , "image" .= imageModels
    ]))

-- | Handle job events (Server-Sent Events)
-- | Streams job progress updates: position, started, progress, preview, complete, error
-- | Per OpenAPI spec: /jobs/{id}/events
handleJobEvents :: GatewayState -> Text -> (Response -> IO t) -> IO t
handleJobEvents gatewayState jobId respond = do
  -- Check if job exists
  mJob <- atomically $ getJob (gsJobStore gatewayState) jobId
  case mJob of
    Nothing -> respond (errorResponse 404 "job_not_found" ("Job not found: " <> jobId) Nothing)
    Just _ -> do
      -- Create SSE response stream
      respond (responseStream status200
        [ (hContentType, "text/event-stream")
        , (hCacheControl, "no-cache")
        , (hConnection, "keep-alive")
        ]
        (streamJobEvents gatewayState jobId))

-- | Stream job events as Server-Sent Events
-- | Events: position, started, progress, preview, complete, error
streamJobEvents :: GatewayState -> Text -> StreamingBody
streamJobEvents gatewayState jobId sendChunk flush = do
  -- Send initial connection event
  connected <- sendSSEEvent sendChunk flush "connected" (object [])
  -- If initial connection event fails, exit early (client disconnected)
  unless connected $ pure ()
  
  -- Monitor job status and send events
  let loop lastStatus lastPosition = do
        mJob <- atomically $ getJob (gsJobStore gatewayState) jobId
        case mJob of
          Nothing -> do
            -- Job deleted, send error and close
            sent <- sendSSEEvent sendChunk flush "error" (object 
              [ "code" .= ("job_not_found" :: Text)
              , "message" .= ("Job was deleted" :: Text)
              ])
            -- Exit loop - job no longer exists (or client disconnected)
            if sent then pure () else pure ()
          Just job -> do
            let currentStatus = qjStatus job
            
            -- Send position update if queued and position changed
            if currentStatus == Queued then do
              position <- atomically $ getQueuePosition (gsQueue gatewayState) jobId
              -- Only send position update if position is valid (>= 0) and changed
              if position >= 0 && position /= lastPosition then do
                let etaSeconds = position * 30 -- Estimate 30s per job
                sent <- sendSSEEvent sendChunk flush "position" (object 
                  [ "position" .= position
                  , "eta_seconds" .= etaSeconds
                  ])
                if sent
                  then loop currentStatus position
                  else pure () -- Client disconnected
              else do
                -- Position is -1 (not in queue) or unchanged, wait and check again
                threadDelay 1000000 -- 1 second
                loop lastStatus lastPosition
            else if currentStatus == Running && lastStatus == Queued then do
              -- Job started
              sent <- sendSSEEvent sendChunk flush "started" (object [])
              if sent
                then loop currentStatus (-1)
                else pure () -- Client disconnected
            else if currentStatus == Running then do
              -- Send progress updates (simplified - in real implementation would get from backend)
              -- For now, send periodic progress updates
              threadDelay 2000000 -- 2 seconds
              sent <- sendSSEEvent sendChunk flush "progress" (object 
                [ "progress" .= (0.5 :: Double)
                , "step" .= (15 :: Int)
                ])
              if sent
                then loop currentStatus (-1)
                else pure () -- Client disconnected
            else if currentStatus == Complete && lastStatus /= Complete then do
              -- Job completed
              let outputUrl = case qjOutput job of
                    Just url -> url
                    Nothing -> "https://cdn.render.weyl.ai/outputs/" <> qjJobId job <> ".mp4"
              sent <- sendSSEEvent sendChunk flush "complete" (object ["output" .= outputUrl])
              -- Close connection after complete (or if client disconnected)
              pure ()
            else if currentStatus == Error && lastStatus /= Error then do
              -- Job errored
              let errorMsg = case qjError job of
                    Just msg -> msg
                    Nothing -> "Unknown error"
              sent <- sendSSEEvent sendChunk flush "error" (object 
                [ "code" .= ("backend_error" :: Text)
                , "message" .= errorMsg
                ])
              -- Close connection after error (or if client disconnected)
              pure ()
            else if currentStatus == Cancelled then do
              -- Job cancelled
              sent <- sendSSEEvent sendChunk flush "error" (object 
                [ "code" .= ("cancelled" :: Text)
                , "message" .= ("Job was cancelled" :: Text)
                ])
              -- Exit loop (or if client disconnected)
              pure ()
            else do
              -- No change, wait and check again
              threadDelay 1000000 -- 1 second
              loop lastStatus lastPosition
  
  -- Start monitoring loop
  initialJob <- atomically $ getJob (gsJobStore gatewayState) jobId
  case initialJob of
    Nothing -> pure ()
    Just job -> do
      let initialStatus = qjStatus job
      initialPosition <- if initialStatus == Queued
        then atomically $ getQueuePosition (gsQueue gatewayState) jobId
        else pure (-1)
      loop initialStatus initialPosition

-- | Send a Server-Sent Event
-- | Format: "event: {eventType}\ndata: {jsonData}\n\n"
-- | Returns False if send failed (e.g., client disconnected), True otherwise
sendSSEEvent :: (LBS.ByteString -> IO ()) -> (IO () -> IO ()) -> Text -> Value -> IO Bool
sendSSEEvent sendChunk flush eventType dataValue = do
  result <- try $ do
    let eventLine = "event: " <> Text.encodeUtf8 eventType <> "\n"
    let dataLine = "data: " <> encode dataValue <> "\n"
    let sseMessage = LBS.fromStrict eventLine <> dataLine <> LBS.singleton 10
    sendChunk sseMessage
    flush (pure ())
  case result of
    Left (_ :: SomeException) -> pure False -- Client disconnected or send failed
    Right _ -> pure True -- Success

-- | Convert backend to model capabilities
backendToModels :: Backend -> [Value]
backendToModels Backend {..} =
  [ object
      [ "family" .= beFamily
      , "model" .= m
      , "modality" .= (if beFamily `elem` ["wan", "qwen"] then "video" :: Text else "image")
      , "backends" .= [Text.pack (show beType)]
      , "status" .= ("active" :: Text)
      ]
  | m <- beModels
  ]

-- | Convert QueuedJob to JobResponse
jobToResponse :: QueuedJob -> JobResponse
jobToResponse QueuedJob {..} = JobResponse
  { jrId = qjJobId
  , jrStatus = statusToText qjStatus
  , jrPosition = Nothing -- Position calculated separately via getQueuePosition
  , jrProgress = case qjStatus of
      Queued -> Just 0.0
      Running -> Just 0.5
      Complete -> Just 1.0
      Error -> Just 0.0
      Cancelled -> Just 0.0
  , jrEtaSeconds = case qjStatus of
      Queued -> Just 30 -- Estimate 30s per job
      _ -> Nothing
  , jrOutput = qjOutput
  , jrOutputs = fmap (:[]) qjOutput
  , jrSeed = Nothing
  , jrError = case qjError of
      Nothing -> Nothing
      Just msg -> Just ErrorDetail
        { edCode = "backend_error"
        , edMessage = msg
        , edRetriable = True
        }
  , jrCreatedAt = Text.pack (show qjCreatedAt)
  , jrStartedAt = fmap (Text.pack . show) qjStartedAt
  , jrCompletedAt = fmap (Text.pack . show) qjCompletedAt
  }

-- | Convert JobStatus to text
statusToText :: JobStatus -> Text
statusToText Queued = "queued"
statusToText Running = "running"
statusToText Complete = "complete"
statusToText Error = "error"
statusToText Cancelled = "cancelled"

-- | Extract customer ID from Authorization header
-- | Decodes JWT token and extracts customer ID from 'sub' claim
-- | Falls back to token hash if JWT decoding fails (for backward compatibility)
extractCustomerId :: Maybe ByteString -> IO Text
extractCustomerId Nothing = pure "anonymous"
extractCustomerId (Just auth) = do
  let authText = Text.decodeUtf8 auth
  if "Bearer " `Text.isPrefixOf` authText
    then do
      let token = Text.drop 7 authText
      -- Attempt JWT decoding
      result <- tryDecodeJWT token
      case result of
        Just customerId -> pure customerId
        Nothing -> do
          -- Fallback: Use token hash as customer ID (for non-JWT tokens)
          pure $ "cust_" <> Text.take 12 token
    else pure "anonymous"
  where
    -- Decode JWT token and extract customer ID from 'sub' claim
    tryDecodeJWT :: Text -> IO (Maybe Text)
    tryDecodeJWT tokenText = do
      result <- try $ do
        -- Decode JWT without verification (we only need to extract customer ID)
        -- In production, signature verification should be done separately
        let tokenBytes = Text.encodeUtf8 tokenText
        
        -- Split JWT into parts: header.payload.signature
        let parts = Text.splitOn "." tokenText
        case parts of
          [_header, payload, _signature] -> do
            -- Decode base64url payload
            case Base64URL.decode (Text.encodeUtf8 payload) of
              Left _ -> pure Nothing
              Right payloadBytes -> do
                -- Parse JSON payload
                case eitherDecode (LBS.fromStrict payloadBytes) of
                  Left _ -> pure Nothing
                  Right (Aeson.Object obj) -> do
                    -- Extract 'sub' claim (subject/customer ID)
                    case KM.lookup "sub" obj of
                      Just (Aeson.String customerId) -> pure (Just customerId)
                      -- Fallback: try 'customer_id' claim
                      _ -> case KM.lookup (fromText "customer_id") obj of
                        Just (Aeson.String customerId) -> pure (Just customerId)
                        -- Fallback: try 'user_id' claim
                        _ -> case KM.lookup (fromText "user_id") obj of
                          Just (Aeson.String customerId) -> pure (Just customerId)
                          _ -> pure Nothing
                  _ -> pure Nothing
          _ -> pure Nothing
      
      case result of
        Left (_ :: SomeException) -> pure Nothing
        Right customerId -> pure customerId

-- | Lookup query parameter
lookupQuery :: Text -> QueryText -> Maybe Text
lookupQuery key params = do
  (_, mVal) <- lookup key params
  mVal

-- | JSON response helper
jsonResponse :: Int -> Value -> Response
jsonResponse code body =
  responseLBS (toEnum code) [(hContentType, "application/json")] (encode body)

-- | JSON response with custom headers
jsonResponseWithHeaders :: Int -> [(ByteString, ByteString)] -> Value -> Response
jsonResponseWithHeaders code headers body =
  responseLBS (toEnum code) ((hContentType, "application/json") : map (\(k,v) -> (mk k, v)) headers) (encode body)
  where
    mk bs = case bs of
      "X-Request-Id" -> "X-Request-Id"
      "Location" -> "Location"
      _ -> "X-Custom"

-- | Error response helper
errorResponse :: Int -> Text -> Text -> Maybe Text -> Response
errorResponse code err msg mReqId =
  jsonResponse code (toJSON (ErrorResponse err msg mReqId))
