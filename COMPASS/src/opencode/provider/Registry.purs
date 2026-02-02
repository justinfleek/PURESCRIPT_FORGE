{-|
Module      : Opencode.Provider.Registry
Description : Provider and model registry
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Provider Registry

Manages provider configurations, model discovery, and SDK initialization.
This is the central coordination point for all LLM providers.

== Coeffect Equation

@
  getProvider : ProviderID -> Graded (State ⊗ Config) (Maybe ProviderInfo)
  getModel    : ProviderID -> ModelID -> Graded (State ⊗ Config) (Maybe ModelInfo)
  getLLMConfig: ProviderID -> ModelID -> Graded (State ⊗ Auth) LLM.ProviderConfig
@

== Supported Providers

| Provider     | Type           | Auth Method       |
|--------------|----------------|-------------------|
| venice       | OpenAI-compat  | Bearer token      |
| openai       | Native         | Bearer token      |
| anthropic    | Native         | API key header    |
| openrouter   | OpenAI-compat  | Bearer token      |
| custom       | OpenAI-compat  | Configurable      |

-}
module Opencode.Provider.Registry
  ( -- * Provider Operations
    getProvider
  , listProviders
  , registerProvider
    -- * Model Operations
  , getModel
  , listModels
    -- * LLM Configuration
  , getLLMConfig
  , defaultLLMConfig
    -- * Built-in Providers
  , veniceProvider
  , openaiProvider
    -- * State
  , RegistryState(..)
  , initialState
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe)
import Data.Either (Either(..))
import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Class (liftEffect)

import Opencode.Session.LLM as LLM

-- ════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ════════════════════════════════════════════════════════════════════════════

-- | Provider identifier
type ProviderID = String

-- | Model identifier
type ModelID = String

-- | Provider information
type ProviderInfo =
  { id :: ProviderID
  , name :: String
  , baseUrl :: String
  , apiType :: ApiType
  , envVars :: Array String      -- Environment variables for API key
  , defaultModel :: Maybe String
  , models :: Array ModelInfo
  }

-- | API type for provider
data ApiType
  = OpenAICompatible  -- Standard OpenAI-compatible API
  | AnthropicNative   -- Anthropic Messages API
  | CustomAPI         -- Custom implementation

derive instance eqApiType :: Eq ApiType

instance showApiType :: Show ApiType where
  show = case _ of
    OpenAICompatible -> "openai-compatible"
    AnthropicNative -> "anthropic"
    CustomAPI -> "custom"

-- | Model information
type ModelInfo =
  { id :: ModelID
  , name :: String
  , contextWindow :: Int
  , maxOutput :: Int
  , supportsTools :: Boolean
  , supportsVision :: Boolean
  , supportsStreaming :: Boolean
  , inputCostPer1M :: Number
  , outputCostPer1M :: Number
  }

-- | Registry state
type RegistryState =
  { providers :: Map ProviderID ProviderInfo
  , apiKeys :: Map ProviderID String
  }

-- ════════════════════════════════════════════════════════════════════════════
-- INITIALIZATION
-- ════════════════════════════════════════════════════════════════════════════

-- | Initial registry state with built-in providers
initialState :: RegistryState
initialState =
  { providers: Map.fromFoldable
      [ { key: "venice", value: veniceProvider }
      , { key: "openai", value: openaiProvider }
      , { key: "openrouter", value: openrouterProvider }
      ]
  , apiKeys: Map.empty
  }

-- | Venice AI provider
veniceProvider :: ProviderInfo
veniceProvider =
  { id: "venice"
  , name: "Venice AI"
  , baseUrl: "https://api.venice.ai/api/v1"
  , apiType: OpenAICompatible
  , envVars: ["VENICE_API_KEY"]
  , defaultModel: Just "llama-3.3-70b"
  , models:
      [ { id: "llama-3.3-70b"
        , name: "Llama 3.3 70B"
        , contextWindow: 131072
        , maxOutput: 16384
        , supportsTools: true
        , supportsVision: false
        , supportsStreaming: true
        , inputCostPer1M: 0.35
        , outputCostPer1M: 0.40
        }
      , { id: "deepseek-r1-671b"
        , name: "DeepSeek R1 671B"
        , contextWindow: 65536
        , maxOutput: 16384
        , supportsTools: true
        , supportsVision: false
        , supportsStreaming: true
        , inputCostPer1M: 2.0
        , outputCostPer1M: 8.0
        }
      , { id: "qwen-2.5-coder-32b"
        , name: "Qwen 2.5 Coder 32B"
        , contextWindow: 131072
        , maxOutput: 16384
        , supportsTools: true
        , supportsVision: false
        , supportsStreaming: true
        , inputCostPer1M: 0.08
        , outputCostPer1M: 0.08
        }
      ]
  }

-- | OpenAI provider
openaiProvider :: ProviderInfo
openaiProvider =
  { id: "openai"
  , name: "OpenAI"
  , baseUrl: "https://api.openai.com/v1"
  , apiType: OpenAICompatible
  , envVars: ["OPENAI_API_KEY"]
  , defaultModel: Just "gpt-4o"
  , models:
      [ { id: "gpt-4o"
        , name: "GPT-4o"
        , contextWindow: 128000
        , maxOutput: 16384
        , supportsTools: true
        , supportsVision: true
        , supportsStreaming: true
        , inputCostPer1M: 2.50
        , outputCostPer1M: 10.0
        }
      , { id: "gpt-4o-mini"
        , name: "GPT-4o Mini"
        , contextWindow: 128000
        , maxOutput: 16384
        , supportsTools: true
        , supportsVision: true
        , supportsStreaming: true
        , inputCostPer1M: 0.15
        , outputCostPer1M: 0.60
        }
      ]
  }

-- | OpenRouter provider
openrouterProvider :: ProviderInfo
openrouterProvider =
  { id: "openrouter"
  , name: "OpenRouter"
  , baseUrl: "https://openrouter.ai/api/v1"
  , apiType: OpenAICompatible
  , envVars: ["OPENROUTER_API_KEY"]
  , defaultModel: Just "anthropic/claude-3.5-sonnet"
  , models: []  -- Dynamic model list from OpenRouter
  }

-- ════════════════════════════════════════════════════════════════════════════
-- PROVIDER OPERATIONS
-- ════════════════════════════════════════════════════════════════════════════

-- | Get provider by ID
getProvider :: ProviderID -> Ref RegistryState -> Effect (Maybe ProviderInfo)
getProvider id stateRef = do
  state <- Ref.read stateRef
  pure $ Map.lookup id state.providers

-- | List all providers
listProviders :: Ref RegistryState -> Effect (Array ProviderInfo)
listProviders stateRef = do
  state <- Ref.read stateRef
  pure $ map _.value $ Map.toUnfoldable state.providers

-- | Register a custom provider
registerProvider :: ProviderInfo -> Ref RegistryState -> Effect Unit
registerProvider provider stateRef = do
  state <- Ref.read stateRef
  Ref.write state { providers = Map.insert provider.id provider state.providers } stateRef

-- ════════════════════════════════════════════════════════════════════════════
-- MODEL OPERATIONS
-- ════════════════════════════════════════════════════════════════════════════

-- | Get model by provider and model ID
getModel :: ProviderID -> ModelID -> Ref RegistryState -> Effect (Maybe ModelInfo)
getModel providerId modelId stateRef = do
  providerM <- getProvider providerId stateRef
  pure $ case providerM of
    Nothing -> Nothing
    Just provider -> Array.find (\m -> m.id == modelId) provider.models

-- | List all models for a provider
listModels :: ProviderID -> Ref RegistryState -> Effect (Array ModelInfo)
listModels providerId stateRef = do
  providerM <- getProvider providerId stateRef
  pure $ case providerM of
    Nothing -> []
    Just provider -> provider.models

-- ════════════════════════════════════════════════════════════════════════════
-- LLM CONFIGURATION
-- ════════════════════════════════════════════════════════════════════════════

-- | Build LLM.ProviderConfig from provider and model
getLLMConfig :: ProviderID -> ModelID -> String -> Ref RegistryState -> Effect LLM.ProviderConfig
getLLMConfig providerId modelId apiKey stateRef = do
  providerM <- getProvider providerId stateRef
  case providerM of
    Nothing -> pure $ defaultLLMConfig modelId apiKey
    Just provider -> pure
      { baseUrl: provider.baseUrl
      , apiKey: apiKey
      , providerId: provider.id
      , headers: buildHeaders provider
      , timeout: 120000
      }
  where
    buildHeaders provider = case provider.id of
      "openrouter" ->
        [ { key: "HTTP-Referer", value: "https://opencode.ai/" }
        , { key: "X-Title", value: "opencode" }
        ]
      _ -> []

-- | Default LLM config (OpenAI-compatible)
defaultLLMConfig :: String -> String -> LLM.ProviderConfig
defaultLLMConfig model apiKey =
  { baseUrl: "https://api.venice.ai/api/v1"
  , apiKey: apiKey
  , providerId: "venice"
  , headers: []
  , timeout: 120000
  }

-- | Set API key for a provider
setApiKey :: ProviderID -> String -> Ref RegistryState -> Effect Unit
setApiKey providerId apiKey stateRef = do
  state <- Ref.read stateRef
  Ref.write state { apiKeys = Map.insert providerId apiKey state.apiKeys } stateRef

-- | Get API key for a provider
getApiKey :: ProviderID -> Ref RegistryState -> Effect (Maybe String)
getApiKey providerId stateRef = do
  state <- Ref.read stateRef
  pure $ Map.lookup providerId state.apiKeys
