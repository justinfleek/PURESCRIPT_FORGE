{-# LANGUAGE StrictData #-}
{-# LANGUAGE OverloadedStrings #-}

-- | Render Gateway Warp HTTP Server
-- | HTTP endpoints for inference gateway per render_specs.pdf
module Render.Gateway.Server where

import Prelude hiding (head, tail)
import Control.Concurrent.STM
import Data.Aeson (encode, decode, Value, ToJSON(..), FromJSON(..))
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy as LBS
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.ByteString as BS
import Network.Wai (Request, Response, requestMethod, pathInfo, requestBody, responseLBS)
import Network.Wai.Handler.Warp (run, Port)
import Network.HTTP.Types (status200, status400, status429, status500, methodPost, methodGet, hContentType)
import Render.Gateway.Core (GatewayState(..), processRequest, handleRequestSuccess, handleRequestFailure)
import Render.Gateway.STM.Queue (QueuedJob(..), Priority(..), enqueueJob)
import Render.Gateway.STM.Clock (readClockSTM)
import Render.Gateway.Backend (Backend(..))
import Data.Time (getCurrentTime)
import Control.Concurrent.STM (atomically)

-- | Start gateway HTTP server
startServer :: Port -> GatewayState -> IO ()
startServer port gatewayState = do
  run port (app gatewayState)

-- | WAI application
app :: GatewayState -> Request -> (Response -> IO t) -> IO t
app gatewayState req respond =
  case (requestMethod req, pathInfo req) of
    (method, ["v1", "generate", "image"]) | method == methodPost ->
      handleGenerateImage gatewayState req respond
    (method, ["v1", "generate", "video"]) | method == methodPost ->
      handleGenerateVideo gatewayState req respond
    (method, ["v1", "jobs", jobId]) | method == methodGet ->
      handleGetJob gatewayState jobId respond
    (method, ["v1", "jobs", jobId, "cancel"]) | method == methodPost ->
      handleCancelJob gatewayState jobId respond
    (method, ["v1", "models"]) | method == methodGet ->
      handleListModels gatewayState respond
    _ ->
      respond (jsonResponse status400 "Not Found" (encode (Text.pack "error" :: Text)))

-- | Handle image generation request
handleGenerateImage :: GatewayState -> Request -> (Response -> IO t) -> IO t
handleGenerateImage gatewayState req respond = do
  body <- requestBody req
  case decode body of
    Nothing -> respond (jsonResponse status400 "Invalid JSON" (encode (Text.pack "error" :: Text)))
    Just requestValue -> do
      -- Parse request and create queued job
      now <- getCurrentTime
      let job = createJobFromRequest requestValue now Normal
      
      -- Enqueue and process
      result <- atomically $ do
        enqueueJob (gsQueue gatewayState) job
        processRequest gatewayState
      
      case result of
        Nothing -> respond (jsonResponse status500 "No backend available" (encode (Text.pack "error" :: Text)))
        Just (queuedJob, backend) -> do
          -- Forward to backend (async)
          forwardToBackend backend queuedJob
          respond (jsonResponse status200 "OK" (encode (Text.pack "job_id", qjRequestId queuedJob)))

-- | Handle video generation request
handleGenerateVideo :: GatewayState -> Request -> (Response -> IO t) -> IO t
handleGenerateVideo = handleGenerateImage -- Same logic

-- | Handle get job status
handleGetJob :: GatewayState -> Text -> (Response -> IO t) -> IO t
handleGetJob _gatewayState _jobId respond = do
  -- TODO: Query job status from storage
  respond (jsonResponse status200 "OK" (encode (Text.pack "status", Text.pack "pending")))

-- | Handle cancel job
handleCancelJob :: GatewayState -> Text -> (Response -> IO t) -> IO t
handleCancelJob _gatewayState _jobId respond = do
  -- TODO: Cancel job
  respond (jsonResponse status200 "OK" (encode (Text.pack "cancelled", True)))

-- | Handle list models
handleListModels :: GatewayState -> (Response -> IO t) -> IO t
handleListModels gatewayState respond = do
  let models = map beId (gsBackends gatewayState)
  respond (jsonResponse status200 "OK" (encode models))

-- | Create job from request
createJobFromRequest :: Value -> UTCTime -> Priority -> QueuedJob
createJobFromRequest requestValue now priority = QueuedJob
  { qjRequestId = Text.pack ("req_" <> show now) -- TODO: Generate UUID
  , qjCustomerId = Text.pack "default" -- TODO: Extract from auth
  , qjModelFamily = Text.pack "flux" -- TODO: Extract from request
  , qjModelName = Text.pack "flux-dev" -- TODO: Extract from request
  , qjTask = Text.pack "t2i" -- TODO: Extract from request
  , qjPriority = priority
  , qjCreatedAt = now
  , qjRequest = Text.decodeUtf8Lenient (LBS.toStrict (encode requestValue))
  }

-- | Forward request to backend
forwardToBackend :: Backend -> QueuedJob -> IO ()
forwardToBackend backend job = do
  -- TODO: Implement gRPC call to Triton backend
  pure ()

-- | JSON response helper
jsonResponse :: Int -> Text -> LBS.ByteString -> Response
jsonResponse statusCode _statusText body = 
  responseLBS statusCode [(hContentType, "application/json")] body
