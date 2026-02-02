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
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Effect.Aff (Aff)
import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, Json)

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
connect :: TritonConfig -> Aff (Either String TritonClient)
connect config = do
  -- TODO: Implement gRPC connection via FFI
  pure $ Right $ TritonClient { config, connected: true }

-- | Disconnect from Triton server
disconnect :: TritonClient -> Aff Unit
disconnect _ = pure unit

-- | Run inference (non-streaming)
infer :: TritonClient -> InferenceRequest -> Aff (Either String InferenceResponse)
infer (TritonClient c) req = do
  -- TODO: Implement gRPC infer via FFI
  pure $ Left "Not implemented: Triton.infer"

-- | Run inference with streaming
inferStream 
  :: TritonClient 
  -> InferenceRequest 
  -> (StreamChunk -> Aff Unit) 
  -> Aff (Either String InferenceResponse)
inferStream client req onChunk = do
  -- TODO: Implement streaming gRPC via FFI
  pure $ Left "Not implemented: Triton.inferStream"

-- | Health check
health :: TritonClient -> Aff Boolean
health (TritonClient c) = do
  -- TODO: HTTP health check
  pure true

-- | Get Prometheus metrics
metrics :: TritonClient -> Aff (Either String String)
metrics (TritonClient c) = do
  -- TODO: HTTP /metrics endpoint
  pure $ Left "Not implemented: Triton.metrics"

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

-- Helper
fromMaybe :: forall a. a -> Maybe a -> a
fromMaybe def = case _ of
  Nothing -> def
  Just a -> a
