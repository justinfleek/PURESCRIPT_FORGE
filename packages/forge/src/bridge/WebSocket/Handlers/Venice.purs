-- | Venice Handlers - Venice AI chat and image generation
module Bridge.WebSocket.Handlers.Venice
  ( handleVeniceChat
  , handleVeniceModels
  , handleVeniceImage
  , ChatRequest
  , ChatResponse
  , StreamResponse
  , Model
  , ImageRequest
  , ImageResponse
  ) where

import Prelude
import Effect.Aff (Aff, launchAff_)
import Effect.Class (liftEffect)
import Effect (Effect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Bridge.WebSocket.Handlers.Types (HandlerContext, JsonRpcResponse, successResponse, errorResponse)
import Bridge.Venice.Client as Venice

-- | Types
type ChatRequest =
  { model :: String
  , messages :: Array { role :: String, content :: String }
  , stream :: Boolean
  , maxTokens :: Maybe Int
  , temperature :: Maybe Number
  }

type ChatResponse =
  { id :: String
  , model :: String
  , choices :: Array { message :: { role :: String, content :: String } }
  , usage :: { promptTokens :: Int, completionTokens :: Int, totalTokens :: Int }
  }

type StreamResponse = { streamId :: String, type_ :: String }
type ChatChunk = { id :: String, choices :: Array { delta :: { content :: Maybe String } } }
type Model =
  { id :: String
  , pricing :: { input :: Number, output :: Number }
  , tier :: String
  , contextLength :: Int
  }
type ImageRequest = { model :: String, prompt :: String, width :: Maybe Int, height :: Maybe Int }
type ImageResponse = { images :: Array String }

-- | FFI declarations (top-level)
foreign import decodeChatRequest :: String -> Effect (Either String ChatRequest)
foreign import encodeChatResponse :: ChatResponse -> String
foreign import encodeStreamResponse :: StreamResponse -> String
foreign import encodeModels :: Array Model -> String
foreign import decodeImageRequest :: String -> Effect (Either String ImageRequest)
foreign import encodeImageResponse :: ImageResponse -> String
foreign import generateStreamId :: Aff String
foreign import processStream :: HandlerContext -> String -> Aff (Maybe ChatChunk) -> Aff Unit

-- | Handle Venice chat
handleVeniceChat :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleVeniceChat ctx params =
  case ctx.veniceClient of
    Nothing -> pure (errorResponse Nothing 5001 "Venice client not available" Nothing)
    Just client ->
      case params of
        Nothing -> pure (errorResponse Nothing 4002 "Missing params" Nothing)
        Just paramsJson -> do
          request <- liftEffect $ decodeChatRequest paramsJson
          case request of
            Left err -> pure (errorResponse Nothing 4003 err Nothing)
            Right req ->
              if req.stream then handleStreamingChat ctx client req
              else handleNonStreamingChat ctx client req

-- | Handle non-streaming chat
handleNonStreamingChat :: HandlerContext -> Venice.VeniceClient -> ChatRequest -> Aff JsonRpcResponse
handleNonStreamingChat _ctx client req = do
  response <- Venice.chat client
    { model: req.model
    , messages: req.messages
    , maxTokens: req.maxTokens
    , temperature: req.temperature
    , stream: false
    }
  case response of
    Left err -> pure (errorResponse Nothing 5002 err Nothing)
    Right resp -> pure (successResponse Nothing (encodeChatResponse resp))

-- | Handle streaming chat
handleStreamingChat :: HandlerContext -> Venice.VeniceClient -> ChatRequest -> Aff JsonRpcResponse
handleStreamingChat ctx client req = do
  streamResult <- Venice.chatStream client
    { model: req.model
    , messages: req.messages
    , maxTokens: req.maxTokens
    , temperature: req.temperature
    , stream: true
    }
  case streamResult of
    Left err -> pure (errorResponse Nothing 5003 err Nothing)
    Right stream -> do
      streamId <- generateStreamId
      launchAff_ $ processStream ctx streamId stream
      pure (successResponse Nothing (encodeStreamResponse { streamId, type_: "stream" }))

-- | Handle Venice models
handleVeniceModels :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleVeniceModels ctx _params =
  case ctx.veniceClient of
    Nothing -> pure (errorResponse Nothing 5001 "Venice client not available" Nothing)
    Just client -> do
      modelsResult <- Venice.listModels client
      case modelsResult of
        Left err -> pure (errorResponse Nothing 5004 err Nothing)
        Right models -> pure (successResponse Nothing (encodeModels models))

-- | Handle Venice image generation
handleVeniceImage :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleVeniceImage ctx params =
  case ctx.veniceClient of
    Nothing -> pure (errorResponse Nothing 5001 "Venice client not available" Nothing)
    Just client ->
      case params of
        Nothing -> pure (errorResponse Nothing 4002 "Missing params" Nothing)
        Just paramsJson -> do
          request <- liftEffect $ decodeImageRequest paramsJson
          case request of
            Left err -> pure (errorResponse Nothing 4003 err Nothing)
            Right req -> do
              result <- Venice.generateImage client req
              case result of
                Left err -> pure (errorResponse Nothing 5005 err Nothing)
                Right images -> pure (successResponse Nothing (encodeImageResponse images))
