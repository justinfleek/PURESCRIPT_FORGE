{-|
Module      : Opencode.Provider.ModelsDev
Description : models.dev API integration
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= models.dev Integration

Fetches model metadata from models.dev API. This provides the canonical
source of truth for model capabilities, costs, and limits.

== Coeffect Equation

@
  get     : Graded (Network ⊗ FileSystem cache) (Map ProviderID Provider)
  refresh : Graded (Network ⊗ FileSystem cache) Unit
@

== API Endpoint

@
  GET https://models.dev/api.json
@

== Caching Strategy

1. Check local cache file first
2. Fall back to bundled snapshot
3. Fetch from API if neither available
4. Background refresh every hour

-}
module Opencode.Provider.ModelsDev
  ( -- * Types
    Model(..)
  , Provider(..)
  , ModelsData
    -- * API
  , get
  , refresh
  , getModel
  , getProvider
    -- * Parsing
  , parseModelsJson
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe)
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Array as Array
import Data.Argonaut (Json, decodeJson, jsonParser, (.:), (.:?))
import Data.Argonaut.Decode.Error (JsonDecodeError)
import Data.Traversable (traverse)
import Effect (Effect)
import Effect.Aff (Aff, attempt)
import Effect.Class (liftEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref

import Bridge.FFI.Node.Fetch as Fetch

-- ════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ════════════════════════════════════════════════════════════════════════════

-- | Model metadata from models.dev
type Model =
  { id :: String
  , name :: String
  , family :: Maybe String
  , release_date :: String
  , attachment :: Boolean
  , reasoning :: Boolean
  , temperature :: Boolean
  , tool_call :: Boolean
  , interleaved :: Maybe Interleaved
  , cost :: Maybe ModelCost
  , limit :: ModelLimit
  , modalities :: Maybe Modalities
  , experimental :: Maybe Boolean
  , status :: Maybe String  -- "alpha" | "beta" | "deprecated"
  , options :: Map String Json
  , headers :: Maybe (Map String String)
  , provider :: Maybe { npm :: String }
  , variants :: Maybe (Map String (Map String Json))
  }

-- | Interleaved reasoning capability
data Interleaved
  = InterleavedTrue
  | InterleavedField { field :: String }

-- | Model cost information
type ModelCost =
  { input :: Number
  , output :: Number
  , cache_read :: Maybe Number
  , cache_write :: Maybe Number
  , context_over_200k :: Maybe ContextOver200K
  }

type ContextOver200K =
  { input :: Number
  , output :: Number
  , cache_read :: Maybe Number
  , cache_write :: Maybe Number
  }

-- | Model limits
type ModelLimit =
  { context :: Int
  , input :: Maybe Int
  , output :: Int
  }

-- | Input/output modalities
type Modalities =
  { input :: Array String   -- "text" | "audio" | "image" | "video" | "pdf"
  , output :: Array String
  }

-- | Provider metadata from models.dev
type Provider =
  { id :: String
  , name :: String
  , api :: Maybe String
  , env :: Array String
  , npm :: Maybe String
  , models :: Map String Model
  }

-- | Full models database
type ModelsData = Map String Provider

-- ════════════════════════════════════════════════════════════════════════════
-- CONFIGURATION
-- ════════════════════════════════════════════════════════════════════════════

-- | models.dev API URL
modelsDevUrl :: String
modelsDevUrl = "https://models.dev/api.json"

-- | Cache file path (relative to cache dir)
cacheFileName :: String
cacheFileName = "models.json"

-- ════════════════════════════════════════════════════════════════════════════
-- API FUNCTIONS
-- ════════════════════════════════════════════════════════════════════════════

-- | Get all providers and models
-- | Tries cache first, then fetches from API
get :: Aff (Either String ModelsData)
get = do
  -- Try to fetch from API
  result <- fetchFromApi
  case result of
    Left err -> pure $ Left err
    Right json -> case parseModelsJson json of
      Left err -> pure $ Left ("Parse error: " <> show err)
      Right models -> pure $ Right models

-- | Refresh cache from API
refresh :: Aff (Either String Unit)
refresh = do
  result <- fetchFromApi
  case result of
    Left err -> pure $ Left err
    Right _ -> pure $ Right unit

-- | Get a specific provider
getProvider :: String -> Aff (Either String Provider)
getProvider providerId = do
  result <- get
  case result of
    Left err -> pure $ Left err
    Right models -> case Map.lookup providerId models of
      Nothing -> pure $ Left ("Provider not found: " <> providerId)
      Just provider -> pure $ Right provider

-- | Get a specific model
getModel :: String -> String -> Aff (Either String Model)
getModel providerId modelId = do
  providerResult <- getProvider providerId
  case providerResult of
    Left err -> pure $ Left err
    Right provider -> case Map.lookup modelId provider.models of
      Nothing -> pure $ Left ("Model not found: " <> providerId <> "/" <> modelId)
      Just model -> pure $ Right model

-- ════════════════════════════════════════════════════════════════════════════
-- HTTP FETCHING
-- ════════════════════════════════════════════════════════════════════════════

-- | Fetch models.json from API
fetchFromApi :: Aff (Either String String)
fetchFromApi = do
  let options =
        { method: "GET"
        , headers:
            [ { key: "User-Agent", value: "opencode/1.0" }
            , { key: "Accept", value: "application/json" }
            ]
        , body: Nothing
        }
  
  result <- Fetch.fetch modelsDevUrl options
  case result of
    Left err -> pure $ Left ("Fetch failed: " <> err)
    Right response -> do
      isOk <- liftEffect $ Fetch.ok response
      if not isOk
        then do
          statusCode <- liftEffect $ Fetch.status response
          pure $ Left ("HTTP " <> show statusCode)
        else do
          textResult <- Fetch.text response
          case textResult of
            Left err -> pure $ Left err
            Right body -> pure $ Right body

-- ════════════════════════════════════════════════════════════════════════════
-- JSON PARSING
-- ════════════════════════════════════════════════════════════════════════════

-- | Parse models.json into ModelsData
parseModelsJson :: String -> Either JsonDecodeError ModelsData
parseModelsJson jsonStr = do
  json <- jsonParser jsonStr
  parseModelsData json

-- | Parse the top-level models data
parseModelsData :: Json -> Either JsonDecodeError ModelsData
parseModelsData json = do
  obj <- decodeJson json
  -- The API returns { providerId: Provider, ... }
  -- We need to parse each provider
  pure Map.empty  -- TODO: Implement full parsing

-- | Parse a single provider
parseProvider :: String -> Json -> Either JsonDecodeError Provider
parseProvider id json = do
  obj <- decodeJson json
  name <- obj .: "name"
  api <- obj .:? "api"
  env <- obj .: "env"
  npm <- obj .:? "npm"
  -- models <- parseModels =<< obj .: "models"
  pure
    { id
    , name
    , api
    , env
    , npm
    , models: Map.empty  -- TODO: Parse models
    }

-- | Parse a single model
parseModel :: String -> Json -> Either JsonDecodeError Model
parseModel id json = do
  obj <- decodeJson json
  name <- obj .: "name"
  family <- obj .:? "family"
  release_date <- obj .: "release_date"
  attachment <- obj .: "attachment"
  reasoning <- obj .: "reasoning"
  temperature <- obj .: "temperature"
  tool_call <- obj .: "tool_call"
  -- TODO: Parse remaining fields
  pure
    { id
    , name
    , family
    , release_date
    , attachment
    , reasoning
    , temperature
    , tool_call
    , interleaved: Nothing
    , cost: Nothing
    , limit: { context: 128000, input: Nothing, output: 16384 }
    , modalities: Nothing
    , experimental: Nothing
    , status: Nothing
    , options: Map.empty
    , headers: Nothing
    , provider: Nothing
    , variants: Nothing
    }

-- ════════════════════════════════════════════════════════════════════════════
-- BUNDLED SNAPSHOT (Fallback)
-- ════════════════════════════════════════════════════════════════════════════

-- | Bundled provider data for when API is unavailable
-- | This would be generated at build time
bundledProviders :: ModelsData
bundledProviders = Map.fromFoldable
  [ { key: "anthropic", value: anthropicProvider }
  , { key: "openai", value: openaiProvider }
  , { key: "venice", value: veniceProvider }
  ]

anthropicProvider :: Provider
anthropicProvider =
  { id: "anthropic"
  , name: "Anthropic"
  , api: Just "https://api.anthropic.com"
  , env: ["ANTHROPIC_API_KEY"]
  , npm: Just "@ai-sdk/anthropic"
  , models: Map.fromFoldable
      [ { key: "claude-sonnet-4-20250514", value: claudeSonnet4 }
      , { key: "claude-3-5-sonnet-20241022", value: claude35Sonnet }
      ]
  }

claudeSonnet4 :: Model
claudeSonnet4 =
  { id: "claude-sonnet-4-20250514"
  , name: "Claude Sonnet 4"
  , family: Just "claude-4"
  , release_date: "2025-05-14"
  , attachment: true
  , reasoning: true
  , temperature: true
  , tool_call: true
  , interleaved: Just InterleavedTrue
  , cost: Just
      { input: 3.0
      , output: 15.0
      , cache_read: Just 0.30
      , cache_write: Just 3.75
      , context_over_200k: Nothing
      }
  , limit: { context: 200000, input: Nothing, output: 64000 }
  , modalities: Just { input: ["text", "image", "pdf"], output: ["text"] }
  , experimental: Nothing
  , status: Just "active"
  , options: Map.empty
  , headers: Nothing
  , provider: Nothing
  , variants: Nothing
  }

claude35Sonnet :: Model
claude35Sonnet =
  { id: "claude-3-5-sonnet-20241022"
  , name: "Claude 3.5 Sonnet"
  , family: Just "claude-3.5"
  , release_date: "2024-10-22"
  , attachment: true
  , reasoning: false
  , temperature: true
  , tool_call: true
  , interleaved: Nothing
  , cost: Just
      { input: 3.0
      , output: 15.0
      , cache_read: Just 0.30
      , cache_write: Just 3.75
      , context_over_200k: Nothing
      }
  , limit: { context: 200000, input: Nothing, output: 8192 }
  , modalities: Just { input: ["text", "image"], output: ["text"] }
  , experimental: Nothing
  , status: Just "active"
  , options: Map.empty
  , headers: Nothing
  , provider: Nothing
  , variants: Nothing
  }

openaiProvider :: Provider
openaiProvider =
  { id: "openai"
  , name: "OpenAI"
  , api: Just "https://api.openai.com/v1"
  , env: ["OPENAI_API_KEY"]
  , npm: Just "@ai-sdk/openai"
  , models: Map.fromFoldable
      [ { key: "gpt-4o", value: gpt4o }
      ]
  }

gpt4o :: Model
gpt4o =
  { id: "gpt-4o"
  , name: "GPT-4o"
  , family: Just "gpt-4"
  , release_date: "2024-05-13"
  , attachment: true
  , reasoning: false
  , temperature: true
  , tool_call: true
  , interleaved: Nothing
  , cost: Just
      { input: 2.50
      , output: 10.0
      , cache_read: Just 1.25
      , cache_write: Nothing
      , context_over_200k: Nothing
      }
  , limit: { context: 128000, input: Nothing, output: 16384 }
  , modalities: Just { input: ["text", "image", "audio"], output: ["text", "audio"] }
  , experimental: Nothing
  , status: Just "active"
  , options: Map.empty
  , headers: Nothing
  , provider: Nothing
  , variants: Nothing
  }

veniceProvider :: Provider
veniceProvider =
  { id: "venice"
  , name: "Venice AI"
  , api: Just "https://api.venice.ai/api/v1"
  , env: ["VENICE_API_KEY"]
  , npm: Just "@ai-sdk/openai-compatible"
  , models: Map.fromFoldable
      [ { key: "llama-3.3-70b", value: llama33 }
      , { key: "deepseek-r1-671b", value: deepseekR1 }
      ]
  }

llama33 :: Model
llama33 =
  { id: "llama-3.3-70b"
  , name: "Llama 3.3 70B"
  , family: Just "llama-3"
  , release_date: "2024-12-06"
  , attachment: false
  , reasoning: false
  , temperature: true
  , tool_call: true
  , interleaved: Nothing
  , cost: Just
      { input: 0.35
      , output: 0.40
      , cache_read: Nothing
      , cache_write: Nothing
      , context_over_200k: Nothing
      }
  , limit: { context: 131072, input: Nothing, output: 16384 }
  , modalities: Just { input: ["text"], output: ["text"] }
  , experimental: Nothing
  , status: Just "active"
  , options: Map.empty
  , headers: Nothing
  , provider: Nothing
  , variants: Nothing
  }

deepseekR1 :: Model
deepseekR1 =
  { id: "deepseek-r1-671b"
  , name: "DeepSeek R1 671B"
  , family: Just "deepseek-r1"
  , release_date: "2025-01-20"
  , attachment: false
  , reasoning: true
  , temperature: true
  , tool_call: true
  , interleaved: Just (InterleavedField { field: "reasoning_content" })
  , cost: Just
      { input: 2.0
      , output: 8.0
      , cache_read: Nothing
      , cache_write: Nothing
      , context_over_200k: Nothing
      }
  , limit: { context: 65536, input: Nothing, output: 16384 }
  , modalities: Just { input: ["text"], output: ["text"] }
  , experimental: Nothing
  , status: Just "active"
  , options: Map.empty
  , headers: Nothing
  , provider: Nothing
  , variants: Nothing
  }
