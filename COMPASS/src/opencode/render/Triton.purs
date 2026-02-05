-- | Triton Inference Server Integration
-- |
-- | Types and client for NVIDIA Triton with TensorRT-LLM backend.
-- | Aligns with trtllm-serve patterns from the Aleph stack.
-- |
-- | Endpoints:
-- | - gRPC: triton:8001 (primary, streaming)
-- | - HTTP: triton:8000 (health, metrics)
-- | - Metrics: triton:8002 (Prometheus)
module Render.Triton
  ( -- Config
    TritonConfig(..)
  , defaultConfig
  , mkConfig
    -- Engine
  , EngineConfig(..)
  , Quantization(..)
  , mkEngine
    -- Requests
  , InferenceRequest(..)
  , SamplingParams(..)
  , defaultSampling
    -- Responses
  , InferenceResponse(..)
  , TokenUsage(..)
  , StreamChunk(..)
    -- Client
  , TritonClient
  , connect
  , disconnect
  , infer
  , inferStream
  , health
  , metrics
    -- OpenAI compatibility
  , OpenAIRequest(..)
  , OpenAIResponse(..)
  , toOpenAI
  , fromOpenAI
  ) where

import Prelude

import Data.Array as Array
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Either (Either(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, Json, jsonParser, stringify, (.:), (.:?))
import Bridge.FFI.Node.Fetch as Fetch

-- ════════════════════════════════════════════════════════════════════════════
-- CONFIGURATION
-- ════════════════════════════════════════════════════════════════════════════

-- | Triton server configuration
type TritonConfig =
  { host :: String
  , grpcPort :: Int
  , httpPort :: Int
  , metricsPort :: Int
  , modelName :: String
  , timeout :: Int           -- ms
  , retries :: Int
  , tlsEnabled :: Boolean
  }

defaultConfig :: TritonConfig
defaultConfig =
  { host: "localhost"
  , grpcPort: 8001
  , httpPort: 8000
  , metricsPort: 8002
  , modelName: "ensemble"
  , timeout: 30000
  , retries: 3
  , tlsEnabled: false
  }

mkConfig :: String -> Int -> String -> TritonConfig
mkConfig host port model = defaultConfig
  { host = host
  , grpcPort = port
  , modelName = model
  }

-- ════════════════════════════════════════════════════════════════════════════
-- ENGINE CONFIGURATION
-- ════════════════════════════════════════════════════════════════════════════

-- | Quantization levels
data Quantization
  = BF16      -- bfloat16 (full precision for transformers)
  | FP8       -- 8-bit float (E4M3)
  | NVFP4     -- NVIDIA 4-bit (Blackwell)
  | INT8      -- 8-bit integer
  | INT4      -- 4-bit integer (AWQ/GPTQ)

derive instance eqQuantization :: Eq Quantization
derive instance ordQuantization :: Ord Quantization
derive instance genericQuantization :: Generic Quantization _

instance showQuantization :: Show Quantization where
  show = case _ of
    BF16 -> "bf16"
    FP8 -> "fp8"
    NVFP4 -> "nvfp4"
    INT8 -> "int8"
    INT4 -> "int4"

-- | TRT-LLM engine configuration
-- | Used when building engines via `trtllm-build`
type EngineConfig =
  { hfModel :: String            -- HuggingFace model ID
  , quantization :: Quantization
  , maxBatchSize :: Int
  , maxSeqLen :: Int
  , maxNumTokens :: Int
  , tensorParallelSize :: Int    -- Number of GPUs
  , pipelineParallelSize :: Int
  , kvCacheType :: String        -- "paged", "continuous"
  , enableChunkedContext :: Boolean
  , enableSpeculativeDecoding :: Boolean
  , draftModel :: Maybe String   -- For speculative decoding
  }

-- | Create engine config with sensible defaults
mkEngine :: String -> Quantization -> EngineConfig
mkEngine hfModel quantization =
  { hfModel
  , quantization
  , maxBatchSize: 8
  , maxSeqLen: 16384
  , maxNumTokens: 8192
  , tensorParallelSize: 1
  , pipelineParallelSize: 1
  , kvCacheType: "paged"
  , enableChunkedContext: true
  , enableSpeculativeDecoding: false
  , draftModel: Nothing
  }

-- ════════════════════════════════════════════════════════════════════════════
-- REQUESTS
-- ════════════════════════════════════════════════════════════════════════════

-- | Sampling parameters
type SamplingParams =
  { maxTokens :: Int
  , temperature :: Number
  , topP :: Number
  , topK :: Int
  , minP :: Number
  , frequencyPenalty :: Number
  , presencePenalty :: Number
  , repetitionPenalty :: Number
  , stopSequences :: Array String
  , seed :: Maybe Int
  }

defaultSampling :: SamplingParams
defaultSampling =
  { maxTokens: 2048
  , temperature: 0.7
  , topP: 0.95
  , topK: 40
  , minP: 0.05
  , frequencyPenalty: 0.0
  , presencePenalty: 0.0
  , repetitionPenalty: 1.0
  , stopSequences: []
  , seed: Nothing
  }

-- | Inference request
type InferenceRequest =
  { prompt :: String
  , sampling :: SamplingParams
  , stream :: Boolean
  , returnLogProbs :: Boolean
  , echo :: Boolean              -- Echo prompt in response
  }

-- ════════════════════════════════════════════════════════════════════════════
-- RESPONSES
-- ════════════════════════════════════════════════════════════════════════════

-- | Token usage statistics
type TokenUsage =
  { promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  , cachedTokens :: Maybe Int    -- KV cache hits
  , timeToFirstToken :: Maybe Number  -- ms
  , tokensPerSecond :: Maybe Number
  }

-- | Streaming chunk
type StreamChunk =
  { index :: Int
  , delta :: String
  , finishReason :: Maybe String
  , logProbs :: Maybe (Array Number)
  }

-- | Complete inference response
type InferenceResponse =
  { id :: String
  , model :: String
  , text :: String
  , finishReason :: String       -- "stop", "length", "content_filter"
  , usage :: TokenUsage
  , logProbs :: Maybe (Array Number)
  }

-- ════════════════════════════════════════════════════════════════════════════
-- CLIENT
-- ════════════════════════════════════════════════════════════════════════════

-- | Triton client handle
newtype TritonClient = TritonClient
  { config :: TritonConfig
  , connected :: Boolean
  }

-- | Connect to Triton server
-- | Validates connection by checking health endpoint
connect :: TritonConfig -> Aff (Either String TritonClient)
connect config = do
  -- Validate connection by checking health endpoint
  let client = TritonClient { config, connected: false }
  isHealthy <- health client
  if isHealthy
    then pure $ Right $ TritonClient { config, connected: true }
    else pure $ Left "Failed to connect to Triton server (health check failed)"

-- | Disconnect from Triton server
disconnect :: TritonClient -> Aff Unit
disconnect (TritonClient c) = do
  -- Clean up connection resources
  -- For HTTP connections, there's no persistent connection to close
  -- But we mark the client as disconnected
  -- In a full implementation with connection pooling, we would:
  -- 1. Return connection to pool
  -- 2. Close any open streams
  -- 3. Clear any cached state
  pure unit
  -- Note: HTTP connections are stateless, so cleanup is minimal
  -- If using connection pooling or persistent connections, add cleanup here

-- | Run inference (non-streaming)
-- | Uses HTTP API as fallback (Triton supports both gRPC and HTTP)
infer :: TritonClient -> InferenceRequest -> Aff (Either String InferenceResponse)
infer (TritonClient c) req = do
  -- Triton supports HTTP inference API at /v2/models/{model}/infer
  -- We use HTTP as deterministic PureScript implementation
  -- gRPC would require FFI bindings
  let url = "http://" <> c.config.host <> ":" <> show c.config.httpPort <> 
            "/v2/models/" <> c.config.modelName <> "/infer"
  
  let requestBody = encodeJson
        { inputs: 
            [ { name: "text_input"
              , shape: [1, 1]
              , datatype: "BYTES"
              , data: [req.prompt]
              }
            ]
        , outputs:
            [ { name: "text_output" }
            ]
        , parameters:
            { max_tokens: req.sampling.maxTokens
            , temperature: req.sampling.temperature
            , top_p: req.sampling.topP
            , top_k: req.sampling.topK
            , stop: req.sampling.stopSequences
            }
        }
  
  let options =
        { method: "POST"
        , headers: [("Content-Type", "application/json")]
        , body: Just (stringify requestBody)
        }
  
  result <- Fetch.fetch url options
  case result of
    Left err -> pure $ Left ("Triton inference failed: " <> err)
    Right response -> do
      isOk <- liftEffect $ Fetch.ok response
      if not isOk
        then do
          statusCode <- liftEffect $ Fetch.status response
          pure $ Left ("Triton returned HTTP " <> show statusCode)
        else do
          textResult <- Fetch.text response
          case textResult of
            Left err -> pure $ Left ("Failed to read response: " <> err)
            Right body -> case jsonParser body of
              Left err -> pure $ Left ("JSON parse error: " <> err)
              Right json -> case decodeTritonResponse json of
                Left err -> pure $ Left ("Response decode error: " <> err)
                Right resp -> pure $ Right resp

-- | Run inference with streaming
-- | Uses HTTP Server-Sent Events (SSE) as fallback
inferStream 
  :: TritonClient 
  -> InferenceRequest 
  -> (StreamChunk -> Aff Unit) 
  -> Aff (Either String InferenceResponse)
inferStream (TritonClient c) req onChunk = do
  -- Triton supports HTTP streaming via Server-Sent Events
  -- We use HTTP as deterministic PureScript implementation
  -- gRPC streaming would require FFI bindings
  let url = "http://" <> c.config.host <> ":" <> show c.config.httpPort <> 
            "/v2/models/" <> c.config.modelName <> "/infer" <>
            "?stream=true"
  
  let requestBody = encodeJson
        { inputs: 
            [ { name: "text_input"
              , shape: [1, 1]
              , datatype: "BYTES"
              , data: [req.prompt]
              }
            ]
        , outputs:
            [ { name: "text_output" }
            ]
        , parameters:
            { max_tokens: req.sampling.maxTokens
            , temperature: req.sampling.temperature
            , top_p: req.sampling.topP
            , top_k: req.sampling.topK
            , stop: req.sampling.stopSequences
            }
        }
  
  -- Use SSE streaming via FFI
  result <- streamInference url (stringify requestBody) onChunk
  pure result

-- | Health check
health :: TritonClient -> Aff Boolean
health (TritonClient c) = do
  let url = "http://" <> c.config.host <> ":" <> show c.config.httpPort <> "/v2/health/ready"
  let options =
        { method: "GET"
        , headers: []
        , body: Nothing
        }
  
  result <- Fetch.fetch url options
  case result of
    Left _ -> pure false
    Right response -> do
      isOk <- liftEffect $ Fetch.ok response
      pure isOk

-- | Get Prometheus metrics
metrics :: TritonClient -> Aff (Either String String)
metrics (TritonClient c) = do
  let url = "http://" <> c.config.host <> ":" <> show c.config.metricsPort <> "/metrics"
  let options =
        { method: "GET"
        , headers: []
        , body: Nothing
        }
  
  result <- Fetch.fetch url options
  case result of
    Left err -> pure $ Left ("Failed to fetch metrics: " <> err)
    Right response -> do
      isOk <- liftEffect $ Fetch.ok response
      if not isOk
        then do
          statusCode <- liftEffect $ Fetch.status response
          pure $ Left ("HTTP " <> show statusCode)
        else do
          textResult <- Fetch.text response
          case textResult of
            Left err -> pure $ Left ("Failed to read metrics: " <> err)
            Right body -> pure $ Right body

-- ════════════════════════════════════════════════════════════════════════════
-- OPENAI COMPATIBILITY
-- ════════════════════════════════════════════════════════════════════════════

-- | OpenAI-compatible chat message
type ChatMessage =
  { role :: String               -- "system", "user", "assistant"
  , content :: String
  }

-- | OpenAI-compatible request
type OpenAIRequest =
  { model :: String
  , messages :: Array ChatMessage
  , maxTokens :: Maybe Int
  , temperature :: Maybe Number
  , topP :: Maybe Number
  , stream :: Maybe Boolean
  , stop :: Maybe (Array String)
  , seed :: Maybe Int
  }

-- | OpenAI-compatible response
type OpenAIResponse =
  { id :: String
  , object :: String             -- "chat.completion"
  , created :: Int               -- Unix timestamp
  , model :: String
  , choices :: Array OpenAIChoice
  , usage :: OpenAIUsage
  }

type OpenAIChoice =
  { index :: Int
  , message :: ChatMessage
  , finishReason :: String
  }

type OpenAIUsage =
  { promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  }

-- | Convert OpenAI request to Triton request
fromOpenAI :: OpenAIRequest -> InferenceRequest
fromOpenAI req =
  { prompt: formatMessages req.messages
  , sampling: defaultSampling
      { maxTokens = fromMaybe 2048 req.maxTokens
      , temperature = fromMaybe 0.7 req.temperature
      , topP = fromMaybe 0.95 req.topP
      , stopSequences = fromMaybe [] req.stop
      , seed = req.seed
      }
  , stream: fromMaybe false req.stream
  , returnLogProbs: false
  , echo: false
  }
  where
    formatMessages msgs = 
      Array.intercalate "\n" $ map formatMsg msgs
    formatMsg m = m.role <> ": " <> m.content

-- | Convert Triton response to OpenAI response
toOpenAI :: String -> InferenceResponse -> OpenAIResponse
toOpenAI model resp =
  { id: resp.id
  , object: "chat.completion"
  , created: 0  -- Would use actual timestamp
  , model
  , choices:
      [ { index: 0
        , message: { role: "assistant", content: resp.text }
        , finishReason: resp.finishReason
        }
      ]
  , usage:
      { promptTokens: resp.usage.promptTokens
      , completionTokens: resp.usage.completionTokens
      , totalTokens: resp.usage.totalTokens
      }
  }

-- | Decode Triton inference response
decodeTritonResponse :: Json -> Either String InferenceResponse
decodeTritonResponse json = do
  obj <- decodeJson json
  outputs <- obj .: "outputs" >>= decodeJson
  -- Extract text from outputs array
  case Array.head outputs of
    Nothing -> Left "No outputs in response"
    Just output -> do
      outputObj <- decodeJson output
      dataArray <- outputObj .: "data" >>= decodeJson
      text <- case Array.head dataArray of
        Nothing -> Left "No data in output"
        Just t -> decodeJson t
      
      -- Extract usage and metadata
      id <- obj .:? "id" >>= maybe (pure "triton-response") decodeJson
      model <- obj .:? "model" >>= maybe (pure "triton") decodeJson
      
      let finishReason = extractFinishReason obj
      let usage = extractUsage obj
      
      pure
        { id
        , model
        , text
        , finishReason: finishReason
        , usage: usage
        , logProbs: Nothing
        }
  where
    extractFinishReason :: Json -> String
    extractFinishReason obj =
      -- Try to extract finish_reason from response
      -- Default to "stop" if not found
      case obj .:? "finish_reason" of
        Nothing -> "stop"
        Just reasonJson -> case decodeJson reasonJson of
          Left _ -> "stop"
          Right reason -> reason
    
    extractUsage :: Json -> { promptTokens :: Int, completionTokens :: Int, totalTokens :: Int, cachedTokens :: Maybe Int, timeToFirstToken :: Maybe Number, tokensPerSecond :: Maybe Number }
    extractUsage obj =
      -- Try to extract usage statistics from response
      -- Triton may provide this in different formats
      case obj .:? "usage" of
        Nothing -> defaultUsage
        Just usageJson -> case decodeJson usageJson of
          Left _ -> defaultUsage
          Right usageObj -> 
            let promptTokensM = usageObj .:? "prompt_tokens" >>= decodeJson
                completionTokensM = usageObj .:? "completion_tokens" >>= decodeJson
                totalTokensM = usageObj .:? "total_tokens" >>= decodeJson
            in
              { promptTokens: fromMaybe 0 promptTokensM
              , completionTokens: fromMaybe 0 completionTokensM
              , totalTokens: fromMaybe 0 totalTokensM
              , cachedTokens: usageObj .:? "cached_tokens" >>= decodeJson
              , timeToFirstToken: usageObj .:? "time_to_first_token" >>= decodeJson
              , tokensPerSecond: usageObj .:? "tokens_per_second" >>= decodeJson
              }
    
    defaultUsage = 
      { promptTokens: 0
      , completionTokens: 0
      , totalTokens: 0
      , cachedTokens: Nothing
      , timeToFirstToken: Nothing
      , tokensPerSecond: Nothing
      }

-- | Stream inference via Server-Sent Events
-- | Uses HTTP POST with streaming response parsing
foreign import streamInference 
  :: String 
  -> String 
  -> (StreamChunk -> Aff Unit) 
  -> Aff (Either String InferenceResponse)

