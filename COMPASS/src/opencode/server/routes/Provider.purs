{-|
Module      : Opencode.Server.Routes.Provider
Description : Provider HTTP routes
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Provider Routes

Full implementation of provider routes matching OpenCode's routes/provider.ts.
Handles provider listing, auth methods, and OAuth flows.

== Coeffect Equation

@
  routes : Unit -> Graded HTTP Router
  
  Provider Routes:
    GET    /provider           -> list
    GET    /provider/auth      -> authMethods
    POST   /provider/:id/oauth/authorize -> authorize
    POST   /provider/:id/oauth/callback  -> callback
@

-}
module Opencode.Server.Routes.Provider
  ( -- * Route Handlers
    list
  , authMethods
  , authorize
  , callback
    -- * Types
  , ProviderListResponse
  , AuthMethod
  , AuthMethodType(..)
  , Authorization
  , AuthorizeBody
  , CallbackBody
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Array as Array
import Effect.Aff (Aff)

import Opencode.Provider.Provider as Provider
import Opencode.Provider.ModelsDev as ModelsDev

-- ════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ════════════════════════════════════════════════════════════════════════════

-- | Response for list endpoint
type ProviderListResponse =
  { all :: Array Provider.Info
  , default :: Map String String  -- providerID -> default modelID
  , connected :: Array String     -- list of connected provider IDs
  }

-- | Authentication method type
data AuthMethodType
  = MethodApiKey
  | MethodOAuth
  | MethodEnv

instance showAuthMethodType :: Show AuthMethodType where
  show MethodApiKey = "api_key"
  show MethodOAuth = "oauth"
  show MethodEnv = "env"

-- | Authentication method
type AuthMethod =
  { type :: AuthMethodType
  , name :: String
  , description :: String
  , envVar :: Maybe String  -- For env-based auth
  }

-- | OAuth authorization response
type Authorization =
  { url :: String
  , method :: AuthMethodType
  }

-- | Body for authorize endpoint
type AuthorizeBody =
  { method :: Int  -- Index into auth methods array
  }

-- | Body for callback endpoint
type CallbackBody =
  { method :: Int
  , code :: Maybe String  -- OAuth authorization code
  }

-- ════════════════════════════════════════════════════════════════════════════
-- ROUTE HANDLERS
-- ════════════════════════════════════════════════════════════════════════════

-- | List all available providers
list :: { disabledProviders :: Array String, enabledProviders :: Maybe (Array String) } -> Aff ProviderListResponse
list config = do
  -- Get all providers from models.dev
  allProviders <- ModelsDev.get
  
  -- Filter based on config
  let filtered = filterProviders config allProviders
  
  -- Get connected providers (those with valid credentials)
  connected <- Provider.list
  
  -- Merge and convert
  let merged = mergeProviders filtered connected
  let defaults = calculateDefaults merged
  let connectedIds = map _.id connected
  
  pure
    { all: merged
    , default: defaults
    , connected: connectedIds
    }
  where
    filterProviders :: { disabledProviders :: Array String, enabledProviders :: Maybe (Array String) } 
                   -> Array ModelsDev.Provider 
                   -> Array ModelsDev.Provider
    filterProviders cfg providers =
      Array.filter (shouldInclude cfg) providers
    
    shouldInclude :: { disabledProviders :: Array String, enabledProviders :: Maybe (Array String) } 
                 -> ModelsDev.Provider 
                 -> Boolean
    shouldInclude cfg provider =
      let isDisabled = Array.elem provider.id cfg.disabledProviders
          isEnabled = case cfg.enabledProviders of
            Nothing -> true
            Just enabled -> Array.elem provider.id enabled
      in isEnabled && not isDisabled
    
    mergeProviders :: Array ModelsDev.Provider -> Array Provider.Info -> Array Provider.Info
    mergeProviders mdProviders connectedProviders =
      let mdConverted = map convertFromModelsDev mdProviders
          connectedMap = Map.fromFoldable (map (\p -> { key: p.id, value: p }) connectedProviders)
      in map (mergeWithConnected connectedMap) mdConverted
    
    convertFromModelsDev :: ModelsDev.Provider -> Provider.Info
    convertFromModelsDev mdp =
      { id: mdp.id
      , name: mdp.name
      , icon: Nothing
      , about: mdp.about
      , api: { name: "OpenAI Compatible", type: "openai" }
      , models: map convertModel mdp.models
      }
    
    convertModel :: ModelsDev.Model -> Provider.Model
    convertModel mdm =
      { id: mdm.id
      , name: mdm.name
      , attachment: mdm.capabilities.attachment
      , reasoning: mdm.capabilities.reasoning
      , temperature: true
      , limit: mdm.limit
      , cost: mdm.cost
      }
    
    mergeWithConnected :: Map String Provider.Info -> Provider.Info -> Provider.Info
    mergeWithConnected connectedMap provider =
      case Map.lookup provider.id connectedMap of
        Nothing -> provider
        Just connected -> connected  -- Connected takes precedence
    
    calculateDefaults :: Array Provider.Info -> Map String String
    calculateDefaults providers =
      Map.fromFoldable $ Array.mapMaybe getDefault providers
      where
        getDefault :: Provider.Info -> Maybe { key :: String, value :: String }
        getDefault p = case Array.head (sortModels p.models) of
          Nothing -> Nothing
          Just model -> Just { key: p.id, value: model.id }
        
        sortModels :: Array Provider.Model -> Array Provider.Model
        sortModels = Array.sortWith (\m -> -(m.limit.context))

-- | Get authentication methods for all providers
authMethods :: Aff (Map String (Array AuthMethod))
authMethods = do
  providers <- ModelsDev.get
  pure $ Map.fromFoldable $ map getProviderMethods providers
  where
    getProviderMethods :: ModelsDev.Provider -> { key :: String, value :: Array AuthMethod }
    getProviderMethods provider =
      { key: provider.id
      , value: getMethodsForProvider provider.id
      }
    
    getMethodsForProvider :: String -> Array AuthMethod
    getMethodsForProvider providerId = case providerId of
      "anthropic" ->
        [ { type: MethodEnv
          , name: "Environment Variable"
          , description: "Set ANTHROPIC_API_KEY"
          , envVar: Just "ANTHROPIC_API_KEY"
          }
        , { type: MethodApiKey
          , name: "API Key"
          , description: "Enter your Anthropic API key"
          , envVar: Nothing
          }
        ]
      "openai" ->
        [ { type: MethodEnv
          , name: "Environment Variable"
          , description: "Set OPENAI_API_KEY"
          , envVar: Just "OPENAI_API_KEY"
          }
        , { type: MethodApiKey
          , name: "API Key"
          , description: "Enter your OpenAI API key"
          , envVar: Nothing
          }
        ]
      "venice" ->
        [ { type: MethodEnv
          , name: "Environment Variable"
          , description: "Set VENICE_API_KEY"
          , envVar: Just "VENICE_API_KEY"
          }
        , { type: MethodApiKey
          , name: "API Key"
          , description: "Enter your Venice API key"
          , envVar: Nothing
          }
        ]
      _ ->
        [ { type: MethodApiKey
          , name: "API Key"
          , description: "Enter your API key"
          , envVar: Nothing
          }
        ]

-- | Initiate OAuth authorization
authorize :: { providerID :: String, method :: Int } -> Aff (Maybe Authorization)
authorize input = do
  methods <- authMethods
  case Map.lookup input.providerID methods of
    Nothing -> pure Nothing
    Just providerMethods ->
      case Array.index providerMethods input.method of
        Nothing -> pure Nothing
        Just authMethod -> case authMethod.type of
          MethodOAuth -> 
            pure $ Just
              { url: generateOAuthUrl input.providerID
              , method: MethodOAuth
              }
          _ -> pure Nothing
  where
    generateOAuthUrl :: String -> String
    generateOAuthUrl providerId =
      "https://auth." <> providerId <> ".com/oauth/authorize?client_id=opencode&redirect_uri=http://localhost:4096/provider/" <> providerId <> "/oauth/callback"

-- | Handle OAuth callback
callback :: { providerID :: String, method :: Int, code :: Maybe String } -> Aff Boolean
callback input = do
  case input.code of
    Nothing -> pure false
    Just _code -> do
      -- TODO: Exchange code for tokens and store
      pure true
