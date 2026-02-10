-- | Venice API Client - Venice AI API Integration
-- | Chat completions (streaming/non-streaming), model listing, image generation
module Bridge.Venice.Client where

import Prelude
import Effect (Effect)
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Bridge.State.Store (StateStore)
import Bridge.FFI.Node.Pino as Pino
import Bridge.FFI.Node.Fetch as Fetch
import Bridge.Venice.RateLimiter (RateLimiter, createRateLimiter)

-- | Opaque Venice Client type
foreign import data VeniceClient :: Type

-- | Chat completion request
type ChatCompletionRequest =
  { model :: String
  , messages :: Array { role :: String, content :: String }
  , maxTokens :: Maybe Int
  , temperature :: Maybe Number
  , stream :: Boolean
  }

-- | Chat completion response
type ChatCompletionResponse =
  { id :: String
  , model :: String
  , choices :: Array { message :: { role :: String, content :: String } }
  , usage :: { promptTokens :: Int, completionTokens :: Int, totalTokens :: Int }
  }

-- | Chat chunk (streaming)
type ChatChunk =
  { id :: String
  , choices :: Array { delta :: { content :: Maybe String } }
  }

-- | Model information
type Model =
  { id :: String
  , pricing :: { input :: Number, output :: Number }
  , tier :: String
  , contextLength :: Int
  }

-- | FFI declarations (top-level)
foreign import createVeniceClientImpl :: String -> StateStore -> Pino.Logger -> RateLimiter -> Effect VeniceClient
foreign import getApiKey :: VeniceClient -> String
foreign import encodeRequest :: ChatCompletionRequest -> String
foreign import encodeStreamRequest :: ChatCompletionRequest -> String
foreign import decodeResponse :: String -> ChatCompletionResponse
foreign import decodeModelsResponse :: String -> Array Model
foreign import encodeImageRequest :: { model :: String, prompt :: String, width :: Maybe Int, height :: Maybe Int } -> String
foreign import decodeImageResponse :: String -> { images :: Array String }
foreign import extractAndUpdateBalance :: VeniceClient -> Fetch.Response -> Effect Unit
foreign import acquireRateLimitImpl :: VeniceClient -> Effect Unit
foreign import parseStream :: Fetch.Response -> Aff (Maybe ChatChunk)

-- | Create Venice client
createVeniceClient :: String -> StateStore -> Pino.Logger -> Effect VeniceClient
createVeniceClient apiKey store logger = do
  rateLimiter <- createRateLimiter
  createVeniceClientImpl apiKey store logger rateLimiter

-- | Chat completion (non-streaming)
chat :: VeniceClient -> ChatCompletionRequest -> Aff (Either String ChatCompletionResponse)
chat client request = do
  liftEffect $ acquireRateLimitImpl client
  response <- Fetch.fetch "https://api.venice.ai/api/v1/chat/completions"
    { method: "POST"
    , headers:
        [ { key: "Authorization", value: "Bearer " <> getApiKey client }
        , { key: "Content-Type", value: "application/json" }
        ]
    , body: Just (encodeRequest request)
    }
  case response of
    Left err -> pure (Left err)
    Right res -> do
      liftEffect $ extractAndUpdateBalance client res
      ok <- liftEffect $ Fetch.ok res
      if ok then do
        jsonStr <- Fetch.json res
        case jsonStr of
          Left err -> pure (Left err)
          Right json -> pure (Right (decodeResponse json))
      else do
        status <- liftEffect $ Fetch.status res
        pure (Left ("HTTP " <> show status))

-- | Chat completion (streaming) - returns stream handler
chatStream :: VeniceClient -> ChatCompletionRequest -> Aff (Either String (Aff (Maybe ChatChunk)))
chatStream client request = do
  liftEffect $ acquireRateLimitImpl client
  response <- Fetch.fetch "https://api.venice.ai/api/v1/chat/completions"
    { method: "POST"
    , headers:
        [ { key: "Authorization", value: "Bearer " <> getApiKey client }
        , { key: "Content-Type", value: "application/json" }
        ]
    , body: Just (encodeStreamRequest request)
    }
  case response of
    Left err -> pure (Left err)
    Right res -> do
      liftEffect $ extractAndUpdateBalance client res
      pure (Right (parseStream res))

-- | List models
listModels :: VeniceClient -> Aff (Either String (Array Model))
listModels client = do
  response <- Fetch.fetch "https://api.venice.ai/api/v1/models"
    { method: "GET"
    , headers: [ { key: "Authorization", value: "Bearer " <> getApiKey client } ]
    , body: Nothing
    }
  case response of
    Left err -> pure (Left err)
    Right res -> do
      liftEffect $ extractAndUpdateBalance client res
      ok <- liftEffect $ Fetch.ok res
      if ok then do
        jsonStr <- Fetch.json res
        case jsonStr of
          Left err -> pure (Left err)
          Right json -> pure (Right (decodeModelsResponse json))
      else do
        status <- liftEffect $ Fetch.status res
        pure (Left ("HTTP " <> show status))

-- | Generate image
generateImage :: VeniceClient -> { model :: String, prompt :: String, width :: Maybe Int, height :: Maybe Int } -> Aff (Either String { images :: Array String })
generateImage client request = do
  response <- Fetch.fetch "https://api.venice.ai/api/v1/images/generations"
    { method: "POST"
    , headers:
        [ { key: "Authorization", value: "Bearer " <> getApiKey client }
        , { key: "Content-Type", value: "application/json" }
        ]
    , body: Just (encodeImageRequest request)
    }
  case response of
    Left err -> pure (Left err)
    Right res -> do
      liftEffect $ extractAndUpdateBalance client res
      ok <- liftEffect $ Fetch.ok res
      if ok then do
        jsonStr <- Fetch.json res
        case jsonStr of
          Left err -> pure (Left err)
          Right json -> pure (Right (decodeImageResponse json))
      else do
        status <- liftEffect $ Fetch.status res
        pure (Left ("HTTP " <> show status))
