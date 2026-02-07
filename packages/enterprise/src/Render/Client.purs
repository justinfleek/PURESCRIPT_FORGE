module Render.Client where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Argonaut (encodeJson, decodeJson, stringify, jsonParser)
import Data.Argonaut.Core as AC
import Render.Types
import Render.FFI (RenderClient, createRenderClientImpl, getApiKey, makeRequest, getHeader, getBody, isOk, parseInt)

-- | Create Render client
createRenderClient :: String -> Effect RenderClient
createRenderClient apiKey = createRenderClientImpl apiKey

-- | Generate video (sync)
generateVideoSync :: RenderClient -> String -> String -> TaskId -> Maybe VideoFormatId -> Maybe BackendId -> VideoGenerateRequest -> Aff (Either String { contentLocation :: Maybe String, requestId :: Maybe RequestId, seed :: Maybe Seed, durationMs :: Maybe Int, body :: String })
generateVideoSync client family model task format backend request = do
  -- Build URL
  let formatStr = case format of
        Nothing -> ""
        Just f -> "?format=" <> show f
  let backendStr = case backend of
        Nothing -> ""
        Just b -> if formatStr == "" then "?backend=" <> show b else "&backend=" <> show b
  let url = "https://sync.render.weyl.ai/video/" <> family <> "/" <> model <> "/" <> show task <> formatStr <> backendStr
  
  -- Encode request
  let body = stringify (encodeJson request)
  
  -- Make request
  response <- makeRequest client "POST" url (Just body)
  
  case response of
    Left err -> pure (Left err)
    Right res -> do
      -- Extract headers
      contentLocation <- liftEffect $ getHeader res "Content-Location"
      requestId <- liftEffect $ getHeader res "X-Weyl-Request-Id"
      seedStr <- liftEffect $ getHeader res "X-Weyl-Seed"
      durationStr <- liftEffect $ getHeader res "X-Weyl-Duration-Ms"
      
      -- Get body (MP4 bytes as base64)
      body <- liftEffect $ getBody res
      
      pure (Right { contentLocation, requestId, seed: seedStr >>= parseInt, durationMs: durationStr >>= parseInt, body })

-- | Generate image (sync)
generateImageSync :: RenderClient -> String -> String -> TaskId -> Maybe ImageFormatId -> Maybe BackendId -> ImageGenerateRequest -> Aff (Either String { contentLocation :: Maybe String, requestId :: Maybe RequestId, seed :: Maybe Seed, durationMs :: Maybe Int, body :: String })
generateImageSync client family model task format backend request = do
  -- Build URL
  let formatStr = case format of
        Nothing -> ""
        Just f -> "?format=" <> show f
  let backendStr = case backend of
        Nothing -> ""
        Just b -> if formatStr == "" then "?backend=" <> show b else "&backend=" <> show b
  let url = "https://sync.render.weyl.ai/image/" <> family <> "/" <> model <> "/" <> show task <> formatStr <> backendStr
  
  -- Encode request
  let body = stringify (encodeJson request)
  
  -- Make request
  response <- makeRequest client "POST" url (Just body)
  
  case response of
    Left err -> pure (Left err)
    Right res -> do
      -- Extract headers
      contentLocation <- liftEffect $ getHeader res "Content-Location"
      requestId <- liftEffect $ getHeader res "X-Weyl-Request-Id"
      seedStr <- liftEffect $ getHeader res "X-Weyl-Seed"
      durationStr <- liftEffect $ getHeader res "X-Weyl-Duration-Ms"
      
      -- Get body (image bytes as base64)
      body <- liftEffect $ getBody res
      
      pure (Right { contentLocation, requestId, seed: seedStr >>= parseInt, durationMs: durationStr >>= parseInt, body })

-- | Queue async job
queueJob :: RenderClient -> AsyncJobRequest -> Aff (Either String JobCreated)
queueJob client request = do
  -- Encode request
  let body = stringify (encodeJson request)
  
  response <- makeRequest client "POST" "https://async.render.weyl.ai/queue" (Just body)
  
  case response of
    Left err -> pure (Left err)
    Right res -> do
      jsonStr <- liftEffect $ getBody res
      case jsonParser jsonStr >>= decodeJson of
        Left err -> pure (Left err)
        Right job -> pure (Right job)

-- | Get job status
getJob :: RenderClient -> JobId -> Aff (Either String Job)
getJob client jobId = do
  response <- makeRequest client "GET" ("https://async.render.weyl.ai/jobs/" <> jobId) Nothing
  
  case response of
    Left err -> pure (Left err)
    Right res -> do
      jsonStr <- liftEffect $ getBody res
      case jsonParser jsonStr >>= decodeJson of
        Left err -> pure (Left err)
        Right job -> pure (Right job)

-- | Cancel job
cancelJob :: RenderClient -> JobId -> Aff (Either String Unit)
cancelJob client jobId = do
  response <- makeRequest client "DELETE" ("https://async.render.weyl.ai/jobs/" <> jobId) Nothing
  
  case response of
    Left err -> pure (Left err)
    Right res -> do
      ok <- liftEffect $ isOk res
      if ok then
        pure (Right unit)
      else
        pure (Left "Failed to cancel job")

-- | List models
listModels :: RenderClient -> Aff (Either String ModelsResponse)
listModels client = do
  response <- makeRequest client "GET" "https://api.render.weyl.ai/models" Nothing
  
  case response of
    Left err -> pure (Left err)
    Right res -> do
      jsonStr <- liftEffect $ getBody res
      case jsonParser jsonStr >>= decodeJson of
        Left err -> pure (Left err)
        Right models -> pure (Right models)

-- | Create upload
createUpload :: RenderClient -> CreateUploadRequest -> Aff (Either String CreateUploadResponse)
createUpload client request = do
  let body = stringify (encodeJson request)
  response <- makeRequest client "POST" "https://api.render.weyl.ai/uploads" (Just body)
  
  case response of
    Left err -> pure (Left err)
    Right res -> do
      jsonStr <- liftEffect $ getBody res
      case jsonParser jsonStr >>= decodeJson of
        Left err -> pure (Left err)
        Right upload -> pure (Right upload)

-- | FFI functions
foreign import data RenderClient :: Type
foreign import createRenderClientImpl :: String -> Effect RenderClient
foreign import getApiKey :: RenderClient -> String
foreign import makeRequest :: RenderClient -> String -> String -> Maybe String -> Aff (Either String Response)
foreign import data Response :: Type
foreign import getHeader :: Response -> String -> Effect (Maybe String)
foreign import getBody :: Response -> Effect String
foreign import isOk :: Response -> Effect Boolean
foreign import parseInt :: String -> Maybe Int
