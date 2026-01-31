{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveGeneric #-}

-- | Render Gateway Warp HTTP Server
-- | HTTP endpoints for inference gateway per render.openapi.yaml
module Render.Gateway.Server where

import Prelude hiding (head, tail)
import Control.Concurrent.STM
import Control.Concurrent (forkIO)
import Control.Exception (try, SomeException)
import Data.Aeson (encode, decode, eitherDecode, Value(..), ToJSON(..), FromJSON(..), (.:), (.:?), (.=), object)
import qualified Data.Aeson as Aeson
import qualified Data.Aeson.KeyMap as KM
import Data.ByteString (ByteString)
import Data.ByteString.Lazy (LazyByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import Network.Wai (Request, Response, requestMethod, pathInfo, rawQueryString, requestBody, responseLBS, requestHeaders, strictRequestBody)
import Network.Wai.Handler.Warp (run, Port)
import Network.HTTP.Types (status200, status201, status400, status404, status429, status500, status503, methodPost, methodGet, methodDelete, hContentType, hAuthorization, QueryText, parseQueryText)
import Network.HTTP.Client (Manager, newManager, defaultManagerSettings, httpLbs, parseRequest, Request(..), RequestBody(..), responseBody, responseStatus)
import Network.HTTP.Types.Status (statusCode)
import Render.Gateway.Core (GatewayState(..), JobStore(..), processRequest, handleRequestSuccess, handleRequestFailure, storeJob, getJob, updateJob, cancelJob, getQueuePosition)
import Render.Gateway.STM.Queue (QueuedJob(..), Priority(..), JobStatus(..), Modality(..), TaskType(..), enqueueJob, queueSize, parseTaskType, parseModality, parsePriority)
import Render.Gateway.STM.Clock (readClockSTM)
import Render.Gateway.Backend (Backend(..), BackendType(..))
import Data.Time (getCurrentTime, UTCTime)
import Data.UUID (UUID)
import Data.UUID.V4 (nextRandom)
import qualified Data.UUID as UUID
import GHC.Generics (Generic)

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
  putStrLn "  POST /jobs/{job_id}/cancel"
  putStrLn "  GET  /models"
  manager <- newManager defaultManagerSettings
  run port (app manager gatewayState)

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

          -- Parse request body
          body <- strictRequestBody req
          case eitherDecode body of
            Left err -> respond (errorResponse 400 "invalid_json" (Text.pack err) Nothing)
            Right requestValue -> do
              -- Extract customer ID from auth header
              let authHeader = lookup hAuthorization (requestHeaders req)
              customerId <- extractCustomerId authHeader

              -- Generate IDs
              jobUuid <- nextRandom
              reqUuid <- nextRandom
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
                    }

              -- Store and enqueue job
              position <- atomically $ do
                storeJob (gsJobStore gatewayState) job
                enqueueJob (gsQueue gatewayState) job
                queueSize (gsQueue gatewayState)

              -- Start async processing
              _ <- forkIO $ processJobAsync manager gatewayState job

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

-- | Process job asynchronously
processJobAsync :: Manager -> GatewayState -> QueuedJob -> IO ()
processJobAsync manager gatewayState job = do
  -- Process through gateway (rate limiting, backend selection)
  result <- atomically $ processRequest gatewayState

  case result of
    Nothing -> do
      -- No backend available, job stays in queue
      -- Could implement retry logic here
      pure ()
    Just (queuedJob, backend) -> do
      -- Forward to backend
      forwardResult <- forwardToBackend manager backend queuedJob
      case forwardResult of
        Left err -> do
          atomically $ handleRequestFailure gatewayState queuedJob backend err
        Right outputUrl -> do
          atomically $ handleRequestSuccess gatewayState queuedJob backend outputUrl

-- | Forward request to inference backend
forwardToBackend :: Manager -> Backend -> QueuedJob -> IO (Either Text Text)
forwardToBackend manager backend job = do
  result <- try $ do
    -- Build request to backend
    let endpoint = Text.unpack (beEndpoint backend)
    let url = "http://" <> endpoint <> "/v2/models/" <> Text.unpack (qjModelName job) <> "/infer"

    initialRequest <- parseRequest url
    let request = initialRequest
          { method = "POST"
          , requestBody = RequestBodyLBS (encode (qjRequest job))
          , requestHeaders =
              [ ("Content-Type", "application/json")
              , ("X-Request-Id", Text.encodeUtf8 (qjRequestId job))
              ]
          }

    -- Send request
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
      code -> pure (Left $ "Backend returned status " <> Text.pack (show code))

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
      let response = jobToResponse job
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
  , jrPosition = if qjStatus == Queued then Just 0 else Nothing
  , jrProgress = case qjStatus of
      Running -> Just 0.5
      Complete -> Just 1.0
      _ -> Nothing
  , jrEtaSeconds = if qjStatus == Queued then Just 30 else Nothing
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
extractCustomerId :: Maybe ByteString -> IO Text
extractCustomerId Nothing = pure "anonymous"
extractCustomerId (Just auth) = do
  -- For now, just extract from Bearer token
  -- Real implementation would decode JWT
  let authText = Text.decodeUtf8 auth
  if "Bearer " `Text.isPrefixOf` authText
    then do
      -- Use token hash as customer ID (simplified)
      let token = Text.drop 7 authText
      pure $ "cust_" <> Text.take 12 token
    else pure "anonymous"

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
