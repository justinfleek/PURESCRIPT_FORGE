{-|
Module      : Opencode.Provider.Provider
Description : Provider system with SDK abstraction
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Provider System

Full provider management matching OpenCode's provider.ts architecture.
Manages SDK loading, model selection, and provider configuration.

== Coeffect Equation

@
  list       : Graded (State ⊗ Config) (Map ProviderID Info)
  getModel   : ProviderID -> ModelID -> Graded State (Maybe Model)
  getLanguage: Model -> Graded (State ⊗ Auth) LanguageModel
@

== Provider Sources (Priority Order)

1. Environment variables (ANTHROPIC_API_KEY, etc.)
2. Auth store (oauth tokens, api keys)
3. Config file (opencode.json provider section)
4. Plugin loaders

== SDK Architecture

@
  ┌─────────────────────────────────────────────────────────────────┐
  │                     Provider.getLanguage(model)                 │
  └────────────────────────────┬────────────────────────────────────┘
                               │
                               ▼
  ┌─────────────────────────────────────────────────────────────────┐
  │                     SDK Cache (by hash)                         │
  │  Map<Hash, SDK>  - reuse SDK instances for same config          │
  └────────────────────────────┬────────────────────────────────────┘
                               │
           ┌───────────────────┼───────────────────┐
           │                   │                   │
           ▼                   ▼                   ▼
  ┌─────────────┐    ┌─────────────┐    ┌─────────────┐
  │ Bundled SDK │    │ Bundled SDK │    │ Dynamic SDK │
  │ (anthropic) │    │ (openai)    │    │ (npm load)  │
  └─────────────┘    └─────────────┘    └─────────────┘
@

-}
module Opencode.Provider.Provider
  ( -- * Types
    Model(..)
  , Info(..)
  , ModelCapabilities(..)
  , ModelCost(..)
  , ModelLimit(..)
  , ApiInfo(..)
  , Source(..)
    -- * Core Functions
  , list
  , getProvider
  , getModel
  , getLanguage
  , getSmallModel
  , defaultModel
    -- * Utilities
  , parseModel
  , sort
  , closest
    -- * State
  , ProviderState(..)
  , initialState
  , initProviders
    -- * Custom Loaders
  , CustomLoader(..)
  , CustomModelLoader
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Array as Array
import Data.String as String
import Data.Tuple (Tuple(..))
import Data.Argonaut (Json, encodeJson)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Class (liftEffect)

import Opencode.Provider.ModelsDev as ModelsDev
import Opencode.Session.LLM as LLM

-- ════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ════════════════════════════════════════════════════════════════════════════

-- | Provider identifier
type ProviderID = String

-- | Model identifier  
type ModelID = String

-- | Where provider config came from
data Source
  = SourceEnv      -- From environment variable
  | SourceConfig   -- From opencode.json
  | SourceCustom   -- From custom loader
  | SourceApi      -- From API key store

derive instance eqSource :: Eq Source

instance showSource :: Show Source where
  show = case _ of
    SourceEnv -> "env"
    SourceConfig -> "config"
    SourceCustom -> "custom"
    SourceApi -> "api"

-- | Model information (matches OpenCode's Provider.Model)
type Model =
  { id :: ModelID
  , providerID :: ProviderID
  , api :: ApiInfo
  , name :: String
  , family :: Maybe String
  , capabilities :: ModelCapabilities
  , cost :: ModelCost
  , limit :: ModelLimit
  , status :: String  -- "alpha" | "beta" | "deprecated" | "active"
  , options :: Map String Json
  , headers :: Map String String
  , release_date :: String
  , variants :: Maybe (Map String (Map String Json))
  }

-- | API endpoint information
type ApiInfo =
  { id :: String      -- Model ID for API
  , url :: String     -- Base URL
  , npm :: String     -- NPM package for SDK
  }

-- | Model capabilities
type ModelCapabilities =
  { temperature :: Boolean
  , reasoning :: Boolean
  , attachment :: Boolean
  , toolcall :: Boolean
  , input :: ModalityCapabilities
  , output :: ModalityCapabilities
  , interleaved :: Interleaved
  }

type ModalityCapabilities =
  { text :: Boolean
  , audio :: Boolean
  , image :: Boolean
  , video :: Boolean
  , pdf :: Boolean
  }

data Interleaved
  = InterleavedBool Boolean
  | InterleavedField { field :: String }

-- | Model cost per 1M tokens
type ModelCost =
  { input :: Number
  , output :: Number
  , cache :: { read :: Number, write :: Number }
  , experimentalOver200K :: Maybe { input :: Number, output :: Number, cache :: { read :: Number, write :: Number } }
  }

-- | Model token limits
type ModelLimit =
  { context :: Int
  , input :: Maybe Int
  , output :: Int
  }

-- | Provider information (matches OpenCode's Provider.Info)
type Info =
  { id :: ProviderID
  , name :: String
  , source :: Source
  , env :: Array String
  , key :: Maybe String
  , options :: Map String Json
  , models :: Map ModelID Model
  }

-- ════════════════════════════════════════════════════════════════════════════
-- STATE MANAGEMENT
-- ════════════════════════════════════════════════════════════════════════════

-- | Provider system state
type ProviderState =
  { providers :: Map ProviderID Info
  , languages :: Map String LanguageModel  -- Cached language models
  , sdkCache :: Map Int SDK                -- SDK instances by config hash
  , modelLoaders :: Map ProviderID CustomModelLoader
  , initialized :: Boolean
  }

-- | Language model abstraction (matches AI SDK's LanguageModelV2)
type LanguageModel =
  { providerId :: String
  , modelId :: String
  , config :: LLM.ProviderConfig
  }

-- | SDK instance (provider factory)
type SDK =
  { languageModel :: String -> LanguageModel
  , chat :: String -> LanguageModel
  , responses :: String -> LanguageModel
  }

-- | Custom model loader function
type CustomModelLoader = SDK -> String -> Map String Json -> Aff LanguageModel

-- | Custom loader configuration
type CustomLoader =
  { autoload :: Boolean
  , getModel :: Maybe CustomModelLoader
  , options :: Map String Json
  }

-- | Initial empty state
initialState :: ProviderState
initialState =
  { providers: Map.empty
  , languages: Map.empty
  , sdkCache: Map.empty
  , modelLoaders: Map.empty
  , initialized: false
  }

-- ════════════════════════════════════════════════════════════════════════════
-- INITIALIZATION
-- ════════════════════════════════════════════════════════════════════════════

-- | Initialize provider state from all sources
initProviders :: Ref ProviderState -> Aff Unit
initProviders stateRef = do
  -- 1. Load models from models.dev
  modelsResult <- ModelsDev.get
  let database = case modelsResult of
        Left _ -> ModelsDev.bundledProviders
        Right models -> models
  
  -- 2. Convert to provider Info
  let providers = Map.mapMaybeWithKey (\k v -> Just (fromModelsDevProvider v)) database
  
  -- 3. Load environment-based providers
  -- TODO: Check env vars and merge
  
  -- 4. Load config-based providers
  -- TODO: Parse opencode.json
  
  -- 5. Run custom loaders
  -- TODO: Anthropic headers, bedrock auth, etc.
  
  -- 6. Update state
  liftEffect $ Ref.modify_ (\s -> s { providers = providers, initialized = true }) stateRef

-- | Convert models.dev Provider to our Info type
fromModelsDevProvider :: ModelsDev.Provider -> Info
fromModelsDevProvider p =
  { id: p.id
  , name: p.name
  , source: SourceCustom
  , env: p.env
  , key: Nothing
  , options: Map.empty
  , models: Map.mapMaybeWithKey (\k v -> Just (fromModelsDevModel p v)) p.models
  }

-- | Convert models.dev Model to our Model type
fromModelsDevModel :: ModelsDev.Provider -> ModelsDev.Model -> Model
fromModelsDevModel provider model =
  { id: model.id
  , providerID: provider.id
  , api:
      { id: model.id
      , url: fromMaybe "" provider.api
      , npm: fromMaybe "@ai-sdk/openai-compatible" (model.provider >>= \p -> Just p.npm)
      }
  , name: model.name
  , family: model.family
  , capabilities:
      { temperature: model.temperature
      , reasoning: model.reasoning
      , attachment: model.attachment
      , toolcall: model.tool_call
      , input: parseModalities (fromMaybe { input: [], output: [] } model.modalities).input
      , output: parseModalities (fromMaybe { input: [], output: [] } model.modalities).output
      , interleaved: case model.interleaved of
          Nothing -> InterleavedBool false
          Just ModelsDev.InterleavedTrue -> InterleavedBool true
          Just (ModelsDev.InterleavedField f) -> InterleavedField f
      }
  , cost:
      { input: fromMaybe 0.0 (model.cost >>= \c -> Just c.input)
      , output: fromMaybe 0.0 (model.cost >>= \c -> Just c.output)
      , cache:
          { read: fromMaybe 0.0 (model.cost >>= _.cache_read)
          , write: fromMaybe 0.0 (model.cost >>= _.cache_write)
          }
      , experimentalOver200K: Nothing
      }
  , limit:
      { context: model.limit.context
      , input: model.limit.input
      , output: model.limit.output
      }
  , status: fromMaybe "active" model.status
  , options: model.options
  , headers: fromMaybe Map.empty model.headers
  , release_date: model.release_date
  , variants: model.variants
  }

-- | Parse modality array to capability record
parseModalities :: Array String -> ModalityCapabilities
parseModalities mods =
  { text: Array.elem "text" mods
  , audio: Array.elem "audio" mods
  , image: Array.elem "image" mods
  , video: Array.elem "video" mods
  , pdf: Array.elem "pdf" mods
  }

-- ════════════════════════════════════════════════════════════════════════════
-- CORE FUNCTIONS
-- ════════════════════════════════════════════════════════════════════════════

-- | List all available providers
list :: Ref ProviderState -> Effect (Map ProviderID Info)
list stateRef = do
  state <- Ref.read stateRef
  pure state.providers

-- | Get provider by ID
getProvider :: ProviderID -> Ref ProviderState -> Effect (Maybe Info)
getProvider id stateRef = do
  state <- Ref.read stateRef
  pure $ Map.lookup id state.providers

-- | Get model by provider and model ID
getModel :: ProviderID -> ModelID -> Ref ProviderState -> Effect (Maybe Model)
getModel providerId modelId stateRef = do
  providerM <- getProvider providerId stateRef
  pure $ case providerM of
    Nothing -> Nothing
    Just provider -> Map.lookup modelId provider.models

-- | Get a language model instance for a model
-- | This is the key function that creates the SDK abstraction
getLanguage :: Model -> Ref ProviderState -> Aff LanguageModel
getLanguage model stateRef = do
  state <- liftEffect $ Ref.read stateRef
  
  -- Check cache first
  let cacheKey = model.providerID <> "/" <> model.id
  case Map.lookup cacheKey state.languages of
    Just cached -> pure cached
    Nothing -> do
      -- Get provider info
      providerM <- liftEffect $ getProvider model.providerID stateRef
      let provider = fromMaybe defaultProviderInfo providerM
      
      -- Build SDK config
      let config = buildSDKConfig model provider
      
      -- Create language model
      let language =
            { providerId: model.providerID
            , modelId: model.id
            , config: config
            }
      
      -- Cache it
      liftEffect $ Ref.modify_ (\s -> s { languages = Map.insert cacheKey language s.languages }) stateRef
      
      pure language

-- | Build SDK configuration for a model
buildSDKConfig :: Model -> Info -> LLM.ProviderConfig
buildSDKConfig model provider =
  { baseUrl: model.api.url
  , apiKey: fromMaybe "" provider.key
  , providerId: model.providerID
  , headers: buildHeaders model provider
  , timeout: 120000
  }

-- | Build headers for a model request
buildHeaders :: Model -> Info -> Array { key :: String, value :: String }
buildHeaders model provider =
  let baseHeaders = map (\(Tuple k v) -> { key: k, value: v }) (Map.toUnfoldable model.headers)
      -- Add provider-specific headers
      providerHeaders = case model.providerID of
        "anthropic" ->
          [ { key: "anthropic-beta"
            , value: "claude-code-20250219,interleaved-thinking-2025-05-14,fine-grained-tool-streaming-2025-05-14"
            }
          ]
        "openrouter" ->
          [ { key: "HTTP-Referer", value: "https://opencode.ai/" }
          , { key: "X-Title", value: "opencode" }
          ]
        "cerebras" ->
          [ { key: "X-Cerebras-3rd-Party-Integration", value: "opencode" } ]
        _ -> []
  in baseHeaders <> providerHeaders

-- | Default provider info when none found
defaultProviderInfo :: Info
defaultProviderInfo =
  { id: "unknown"
  , name: "Unknown"
  , source: SourceCustom
  , env: []
  , key: Nothing
  , options: Map.empty
  , models: Map.empty
  }

-- ════════════════════════════════════════════════════════════════════════════
-- MODEL SELECTION
-- ════════════════════════════════════════════════════════════════════════════

-- | Get a small/fast model for the same provider
getSmallModel :: ProviderID -> Ref ProviderState -> Effect (Maybe Model)
getSmallModel providerId stateRef = do
  providerM <- getProvider providerId stateRef
  case providerM of
    Nothing -> pure Nothing
    Just provider -> do
      let priority = ["claude-haiku-4-5", "claude-haiku-4.5", "3-5-haiku", "gpt-4o-mini", "gemini-2.5-flash"]
      let models = Map.values provider.models
      pure $ findByPriority priority models

-- | Find model matching any priority string
findByPriority :: Array String -> Array Model -> Maybe Model
findByPriority priorities models =
  Array.head $ Array.mapMaybe findOne priorities
  where
    findOne p = Array.find (\m -> String.contains (String.Pattern p) m.id) models

-- | Get default model for a provider or across all providers
defaultModel :: Ref ProviderState -> Effect (Maybe { providerID :: String, modelID :: String })
defaultModel stateRef = do
  providers <- list stateRef
  let allModels = Array.concatMap (\p -> Array.fromFoldable $ Map.values p.models) (Array.fromFoldable $ Map.values providers)
  let sorted = sort allModels
  pure $ Array.head sorted >>= \m -> Just { providerID: m.providerID, modelID: m.id }

-- | Sort models by preference
sort :: Array Model -> Array Model
sort models =
  let priority = ["gpt-5", "claude-sonnet-4", "gemini-2-pro", "deepseek-r1"]
      scored = map (\m -> Tuple (scoreModel priority m) m) models
      sorted = Array.sortWith (\(Tuple s _) -> negate s) scored
  in map (\(Tuple _ m) -> m) sorted

-- | Score a model based on priority list
scoreModel :: Array String -> Model -> Int
scoreModel priorities model =
  case Array.findIndex (\p -> String.contains (String.Pattern p) model.id) priorities of
    Nothing -> 0
    Just idx -> 100 - idx

-- | Find closest model to a query
closest :: ProviderID -> Array String -> Ref ProviderState -> Effect (Maybe { providerID :: String, modelID :: String })
closest providerId queries stateRef = do
  providerM <- getProvider providerId stateRef
  case providerM of
    Nothing -> pure Nothing
    Just provider -> do
      let models = Array.fromFoldable $ Map.keys provider.models
      pure $ Array.head $ Array.mapMaybe (findInModels models) queries
  where
    findInModels models query =
      Array.find (\m -> String.contains (String.Pattern query) m) models
        >>= \m -> Just { providerID: providerId, modelID: m }

-- ════════════════════════════════════════════════════════════════════════════
-- UTILITIES
-- ════════════════════════════════════════════════════════════════════════════

-- | Parse "provider/model" string
parseModel :: String -> { providerID :: String, modelID :: String }
parseModel input =
  case String.split (String.Pattern "/") input of
    [provider, model] -> { providerID: provider, modelID: model }
    [provider] -> { providerID: provider, modelID: "" }
    parts -> case Array.uncons parts of
      Nothing -> { providerID: "", modelID: "" }
      Just { head, tail } -> { providerID: head, modelID: String.joinWith "/" tail }
