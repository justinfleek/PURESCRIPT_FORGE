-- | Venice API Client - Venice AI API Integration
-- |
-- | **What:** Provides a PureScript client for Venice AI API, supporting chat
-- |         completions (streaming and non-streaming), model listing, and image
-- |         generation. Includes rate limiting and automatic balance updates.
-- | **Why:** Enables Bridge Server to interact with Venice AI API for chat,
-- |         model information, and image generation. Integrates with state store
-- |         to update balance automatically.
-- | **How:** Uses HTTP requests via Fetch API, handles streaming responses,
-- |         implements rate limiting, and updates state store with balance changes.
-- |
-- | **Dependencies:**
-- | - `Bridge.FFI.Node.Fetch`: HTTP request functionality
-- | - `Bridge.State.Store`: State store for balance updates
-- | - `Bridge.Venice.RateLimiter`: Rate limiting for API calls
-- |
-- | **Mathematical Foundation:**
-- | - **Rate Limiting:** Uses token bucket algorithm to limit API calls per minute.
-- |   Rate limits are updated from API response headers.
-- | - **Balance Updates:** Balance is updated after each API call based on usage
-- |   information in response.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Bridge.Venice.Client as Venice
-- |
-- | -- Create client
-- | client <- Venice.createVeniceClient apiKey store logger
-- |
-- | -- Chat completion
-- | response <- Venice.chat client {
-- |   model: "gpt-4"
-- |   , messages: [{ role: "user", content: "Hello" }]
-- |   , stream: false
-- |   }
-- |
-- | -- List models
-- | models <- Venice.listModels client
-- | ```
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
import Bridge.Venice.RateLimiter (RateLimiter, createRateLimiter, acquireRateLimit, updateFromResponse)

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

foreign import createVeniceClientImpl :: String -> StateStore -> Pino.Logger -> RateLimiter -> Effect VeniceClient

-- | Create Venice client
createVeniceClient :: String -> StateStore -> Pino.Logger -> Effect VeniceClient
createVeniceClient apiKey store logger = do
  rateLimiter <- createRateLimiter
  createVeniceClientImpl apiKey store logger rateLimiter

-- | FFI functions
foreign import getApiKey :: VeniceClient -> String
foreign import encodeRequest :: ChatCompletionRequest -> String
foreign import decodeResponse :: String -> ChatCompletionResponse
foreign import extractAndUpdateBalance :: VeniceClient -> Fetch.Response -> Effect Unit
foreign import acquireRateLimit :: VeniceClient -> Effect Unit

-- | Chat completion (non-streaming)
chat :: VeniceClient -> ChatCompletionRequest -> Aff (Either String ChatCompletionResponse)
chat client request = do
  -- Acquire rate limit
  liftEffect $ acquireRateLimit client
  
  -- Make request
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
      -- Extract balance from headers
      liftEffect $ extractAndUpdateBalance client res
      
      -- Check if OK
      ok <- liftEffect $ Fetch.ok res
      if ok then do
        jsonStr <- Fetch.json res
        case jsonStr of
          Left err -> pure (Left err)
          Right json -> pure (Right (decodeResponse json))
      else do
        status <- liftEffect $ Fetch.status res
        pure (Left ("HTTP " <> show status))

foreign import encodeStreamRequest :: ChatCompletionRequest -> String
foreign import parseStream :: Fetch.Response -> Aff (Maybe ChatChunk)

-- | Chat completion (streaming)
chatStream :: VeniceClient -> ChatCompletionRequest -> Aff (Either String (Aff (Maybe ChatChunk)))
chatStream client request = do
  -- Acquire rate limit
  liftEffect $ acquireRateLimit client
  
  -- Make streaming request
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
      -- Extract balance from headers
      liftEffect $ extractAndUpdateBalance client res
      
      -- Return stream handler
      pure (Right (parseStream res))

foreign import decodeModelsResponse :: String -> Array Model

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

foreign import encodeImageRequest :: { model :: String, prompt :: String, width :: Maybe Int, height :: Maybe Int } -> String
foreign import decodeImageResponse :: String -> { images :: Array String }

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
