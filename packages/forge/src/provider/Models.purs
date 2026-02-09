-- | Provider Models
-- | Ported from: opencode-dev/packages/opencode/src/provider/provider.ts (models section)
module Forge.Provider.Models 
  ( -- * Types
    ModelInfo
  , ModelCapabilities
  , InputCapabilities
  , OutputCapabilities
  , ModelLimits
  , ModelCost
  , ModelStatus(..)
  , ProviderInfo
    -- * Functions
  , listModels
  , getProviderModels
  , getModel
  , listProviders
  , getProvider
  , isModelConnected
    -- * Built-in Providers
  , builtinProviders
  , popularModels
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Model status
data ModelStatus 
  = Active
  | Beta
  | Alpha
  | Deprecated
  | Preview

derive instance eqModelStatus :: Eq ModelStatus

instance showModelStatus :: Show ModelStatus where
  show Active = "active"
  show Beta = "beta"
  show Alpha = "alpha"
  show Deprecated = "deprecated"
  show Preview = "preview"

-- | Input capabilities
type InputCapabilities =
  { text :: Boolean
  , audio :: Boolean
  , image :: Boolean
  , video :: Boolean
  , pdf :: Boolean
  }

-- | Output capabilities
type OutputCapabilities =
  { text :: Boolean
  , audio :: Boolean
  , image :: Boolean
  , video :: Boolean
  , pdf :: Boolean
  }

-- | Model capabilities
type ModelCapabilities =
  { temperature :: Boolean
  , reasoning :: Boolean
  , attachment :: Boolean
  , toolcall :: Boolean
  , streaming :: Boolean
  , systemPrompt :: Boolean
  , input :: InputCapabilities
  , output :: OutputCapabilities
  }

-- | Model cost (per million tokens)
type ModelCost =
  { input :: Number
  , output :: Number
  , cacheRead :: Number
  , cacheWrite :: Number
  }

-- | Model limits
type ModelLimits =
  { context :: Int
  , input :: Maybe Int
  , output :: Int
  }

-- | Model information
type ModelInfo =
  { id :: String
  , name :: String
  , provider :: String
  , family :: Maybe String
  , capabilities :: ModelCapabilities
  , cost :: ModelCost
  , limits :: ModelLimits
  , status :: ModelStatus
  , releaseDate :: Maybe String
  }

-- | Provider information
type ProviderInfo =
  { id :: String
  , name :: String
  , website :: String
  , apiKeyEnvVar :: String
  , apiKeyRequired :: Boolean
  , supportsCustomModels :: Boolean
  }

-- ============================================================================
-- BUILT-IN DATA
-- ============================================================================

-- | Built-in providers
builtinProviders :: Array ProviderInfo
builtinProviders =
  [ { id: "anthropic"
    , name: "Anthropic"
    , website: "https://anthropic.com"
    , apiKeyEnvVar: "ANTHROPIC_API_KEY"
    , apiKeyRequired: true
    , supportsCustomModels: false
    }
  , { id: "openai"
    , name: "OpenAI"
    , website: "https://openai.com"
    , apiKeyEnvVar: "OPENAI_API_KEY"
    , apiKeyRequired: true
    , supportsCustomModels: false
    }
  , { id: "google"
    , name: "Google"
    , website: "https://ai.google.dev"
    , apiKeyEnvVar: "GOOGLE_API_KEY"
    , apiKeyRequired: true
    , supportsCustomModels: false
    }
  , { id: "amazon-bedrock"
    , name: "Amazon Bedrock"
    , website: "https://aws.amazon.com/bedrock"
    , apiKeyEnvVar: "AWS_ACCESS_KEY_ID"
    , apiKeyRequired: true
    , supportsCustomModels: false
    }
  , { id: "azure"
    , name: "Azure OpenAI"
    , website: "https://azure.microsoft.com/services/openai"
    , apiKeyEnvVar: "AZURE_API_KEY"
    , apiKeyRequired: true
    , supportsCustomModels: true
    }
  , { id: "openrouter"
    , name: "OpenRouter"
    , website: "https://openrouter.ai"
    , apiKeyEnvVar: "OPENROUTER_API_KEY"
    , apiKeyRequired: true
    , supportsCustomModels: true
    }
  , { id: "groq"
    , name: "Groq"
    , website: "https://groq.com"
    , apiKeyEnvVar: "GROQ_API_KEY"
    , apiKeyRequired: true
    , supportsCustomModels: false
    }
  , { id: "mistral"
    , name: "Mistral"
    , website: "https://mistral.ai"
    , apiKeyEnvVar: "MISTRAL_API_KEY"
    , apiKeyRequired: true
    , supportsCustomModels: false
    }
  , { id: "xai"
    , name: "xAI"
    , website: "https://x.ai"
    , apiKeyEnvVar: "XAI_API_KEY"
    , apiKeyRequired: true
    , supportsCustomModels: false
    }
  , { id: "deepseek"
    , name: "DeepSeek"
    , website: "https://deepseek.com"
    , apiKeyEnvVar: "DEEPSEEK_API_KEY"
    , apiKeyRequired: true
    , supportsCustomModels: false
    }
  , { id: "together"
    , name: "Together AI"
    , website: "https://together.ai"
    , apiKeyEnvVar: "TOGETHER_API_KEY"
    , apiKeyRequired: true
    , supportsCustomModels: true
    }
  , { id: "ollama"
    , name: "Ollama"
    , website: "https://ollama.ai"
    , apiKeyEnvVar: ""
    , apiKeyRequired: false
    , supportsCustomModels: true
    }
  ]

-- | Default model capabilities
defaultCapabilities :: ModelCapabilities
defaultCapabilities =
  { temperature: true
  , reasoning: false
  , attachment: false
  , toolcall: true
  , streaming: true
  , systemPrompt: true
  , input: { text: true, audio: false, image: false, video: false, pdf: false }
  , output: { text: true, audio: false, image: false, video: false, pdf: false }
  }

-- | Popular models
popularModels :: Array ModelInfo
popularModels =
  [ -- Anthropic Claude models
    { id: "claude-sonnet-4-20250514"
    , name: "Claude Sonnet 4"
    , provider: "anthropic"
    , family: Just "claude"
    , capabilities: defaultCapabilities 
        { attachment = true
        , reasoning = true
        , input { image = true, pdf = true }
        }
    , cost: { input: 3.0, output: 15.0, cacheRead: 0.3, cacheWrite: 3.75 }
    , limits: { context: 200000, input: Nothing, output: 64000 }
    , status: Active
    , releaseDate: Just "2025-05-14"
    }
  , { id: "claude-opus-4-20250514"
    , name: "Claude Opus 4"
    , provider: "anthropic"
    , family: Just "claude"
    , capabilities: defaultCapabilities 
        { attachment = true
        , reasoning = true
        , input { image = true, pdf = true }
        }
    , cost: { input: 15.0, output: 75.0, cacheRead: 1.5, cacheWrite: 18.75 }
    , limits: { context: 200000, input: Nothing, output: 32000 }
    , status: Active
    , releaseDate: Just "2025-05-14"
    }
  , { id: "claude-3-5-sonnet-20241022"
    , name: "Claude 3.5 Sonnet"
    , provider: "anthropic"
    , family: Just "claude"
    , capabilities: defaultCapabilities 
        { attachment = true
        , input { image = true, pdf = true }
        }
    , cost: { input: 3.0, output: 15.0, cacheRead: 0.3, cacheWrite: 3.75 }
    , limits: { context: 200000, input: Nothing, output: 8192 }
    , status: Active
    , releaseDate: Just "2024-10-22"
    }
  , { id: "claude-3-5-haiku-20241022"
    , name: "Claude 3.5 Haiku"
    , provider: "anthropic"
    , family: Just "claude"
    , capabilities: defaultCapabilities 
        { attachment = true
        , input { image = true }
        }
    , cost: { input: 1.0, output: 5.0, cacheRead: 0.1, cacheWrite: 1.25 }
    , limits: { context: 200000, input: Nothing, output: 8192 }
    , status: Active
    , releaseDate: Just "2024-10-22"
    }
  -- OpenAI models
  , { id: "gpt-4o"
    , name: "GPT-4o"
    , provider: "openai"
    , family: Just "gpt-4"
    , capabilities: defaultCapabilities 
        { attachment = true
        , input { image = true, audio = true }
        , output { audio = true }
        }
    , cost: { input: 2.5, output: 10.0, cacheRead: 1.25, cacheWrite: 2.5 }
    , limits: { context: 128000, input: Nothing, output: 16384 }
    , status: Active
    , releaseDate: Just "2024-05-13"
    }
  , { id: "gpt-4o-mini"
    , name: "GPT-4o Mini"
    , provider: "openai"
    , family: Just "gpt-4"
    , capabilities: defaultCapabilities 
        { attachment = true
        , input { image = true }
        }
    , cost: { input: 0.15, output: 0.6, cacheRead: 0.075, cacheWrite: 0.15 }
    , limits: { context: 128000, input: Nothing, output: 16384 }
    , status: Active
    , releaseDate: Just "2024-07-18"
    }
  , { id: "o1"
    , name: "o1"
    , provider: "openai"
    , family: Just "o1"
    , capabilities: defaultCapabilities 
        { reasoning = true
        , attachment = true
        , input { image = true }
        , temperature = false
        }
    , cost: { input: 15.0, output: 60.0, cacheRead: 7.5, cacheWrite: 15.0 }
    , limits: { context: 200000, input: Nothing, output: 100000 }
    , status: Active
    , releaseDate: Just "2024-12-05"
    }
  , { id: "o3-mini"
    , name: "o3-mini"
    , provider: "openai"
    , family: Just "o3"
    , capabilities: defaultCapabilities 
        { reasoning = true
        , temperature = false
        }
    , cost: { input: 1.1, output: 4.4, cacheRead: 0.55, cacheWrite: 1.1 }
    , limits: { context: 200000, input: Nothing, output: 100000 }
    , status: Active
    , releaseDate: Just "2025-01-31"
    }
  -- Google models
  , { id: "gemini-2.0-flash"
    , name: "Gemini 2.0 Flash"
    , provider: "google"
    , family: Just "gemini"
    , capabilities: defaultCapabilities 
        { attachment = true
        , input { image = true, audio = true, video = true }
        }
    , cost: { input: 0.1, output: 0.4, cacheRead: 0.025, cacheWrite: 0.1 }
    , limits: { context: 1000000, input: Nothing, output: 8192 }
    , status: Active
    , releaseDate: Just "2024-12-11"
    }
  , { id: "gemini-2.5-pro-preview"
    , name: "Gemini 2.5 Pro Preview"
    , provider: "google"
    , family: Just "gemini"
    , capabilities: defaultCapabilities 
        { attachment = true
        , reasoning = true
        , input { image = true, audio = true, video = true }
        }
    , cost: { input: 1.25, output: 10.0, cacheRead: 0.3125, cacheWrite: 1.25 }
    , limits: { context: 1000000, input: Nothing, output: 65536 }
    , status: Preview
    , releaseDate: Just "2025-03-25"
    }
  ]

-- ============================================================================
-- FUNCTIONS
-- ============================================================================

-- | List all available models
listModels :: Aff (Either String (Array ModelInfo))
listModels = do
  -- Return built-in models + any custom models from FFI
  customModels <- listCustomModelsFFI
  case customModels of
    Left err -> pure $ Right popularModels  -- Fall back to built-ins
    Right customs -> pure $ Right (popularModels <> customs)

foreign import listCustomModelsFFI :: Aff (Either String (Array ModelInfo))

-- | Get models for a specific provider
getProviderModels :: String -> Aff (Either String (Array ModelInfo))
getProviderModels providerId = do
  allModels <- listModels
  case allModels of
    Left err -> pure $ Left err
    Right models -> pure $ Right $ Array.filter (\m -> m.provider == providerId) models

-- | Get model info by ID
getModel :: String -> Aff (Either String ModelInfo)
getModel modelId = do
  allModels <- listModels
  case allModels of
    Left err -> pure $ Left err
    Right models -> case Array.find (\m -> m.id == modelId) models of
      Nothing -> pure $ Left $ "Model not found: " <> modelId
      Just model -> pure $ Right model

-- | List all providers
listProviders :: Aff (Either String (Array ProviderInfo))
listProviders = pure $ Right builtinProviders

-- | Get provider info by ID
getProvider :: String -> Maybe ProviderInfo
getProvider providerId = Array.find (\p -> p.id == providerId) builtinProviders

-- | Check if a model is connected (has API key configured)
isModelConnected :: String -> Aff Boolean
isModelConnected modelId = do
  modelResult <- getModel modelId
  case modelResult of
    Left _ -> pure false
    Right model -> case getProvider model.provider of
      Nothing -> pure false
      Just provider ->
        if not provider.apiKeyRequired then
          pure true
        else
          checkApiKeyFFI provider.apiKeyEnvVar

foreign import checkApiKeyFFI :: String -> Aff Boolean
