-- | Omega V1 Models Route Handler
-- |
-- | Lists available Omega models, filtering out disabled ones for authenticated users.
-- | Pure PureScript implementation - NO FFI (except framework boundary)
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/v1/models.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.V1.Models
  ( handleModelsGET
  , handleModelsOPTIONS
  , ModelInfo
  , ModelsResponse
  , extractApiKey
  , filterEnabledModels
  , formatModelInfo
  ) where

import Prelude

import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Array (filter, map, elem)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), split, toLower)
import Data.String.CodeUnits (length, take)
import Foreign.Object as Object
import Console.App.FFI.SolidStart (APIEvent, Response)

-- | Model information
type ModelInfo =
  { id :: String
  , object :: String
  , created :: Int
  , owned_by :: String
  }

-- | Models list response
type ModelsResponse =
  { object :: String
  , data :: Array ModelInfo
  }

-- | Extract API key from Authorization header (pure)
-- | Format: "Bearer <key>" or "bearer <key>"
extractApiKey :: String -> Maybe String
extractApiKey header =
  let parts = split (Pattern " ") (toLower header)
  in case parts of
       [bearer, key] | bearer == "bearer" -> Just key
       _ -> Nothing

-- | Check if model ID is in disabled list (pure)
isDisabled :: String -> Array String -> Boolean
isDisabled modelId disabled = elem modelId disabled

-- | Format model info with timestamp (pure)
formatModelInfo :: Int -> String -> ModelInfo
formatModelInfo timestamp id =
  { id: id
  , object: "model"
  , created: timestamp
  , owned_by: "opencode"
  }

-- | Filter enabled models from model IDs and disabled list (pure)
filterEnabledModels :: Array String -> Array String -> Array String
filterEnabledModels modelIds disabledModels =
  filter (\id -> not (isDisabled id disabledModels)) modelIds

-- | Build models response from enabled model IDs and timestamp (pure)
buildModelsResponse :: Array String -> Int -> ModelsResponse
buildModelsResponse enabledIds timestamp =
  { object: "list"
  , data: map (formatModelInfo timestamp) enabledIds
  }

-- | Omega data models list (pure PureScript type)
type OmegaModelsData = { models :: Object.Object (Array String) }

-- | FFI: Get Omega data models list (framework boundary - converts to PureScript types immediately)
foreign import omegaDataList :: Effect OmegaModelsData

-- | FFI: Get disabled models for API key (database operation - uses Database DSL)
foreign import getDisabledModels :: String -> Aff (Array String)

-- | FFI: Get current timestamp in seconds (system boundary)
foreign import getCurrentTimestamp :: Effect Int

-- | Extract model IDs from Omega data (pure PureScript)
getModelIdsFromRecord :: OmegaModelsData -> Array String
getModelIdsFromRecord omegaData = Object.keys omegaData.models

-- | FFI: Convert response to JSON string (framework boundary - HTTP response)
foreign import toJsonString :: ModelsResponse -> String

-- | FFI: Create JSON response (framework boundary)
foreign import jsonResponse :: String -> Aff Response

-- | FFI: Create text response (framework boundary)
foreign import textResponse :: String -> Int -> Aff Response

-- | FFI: Get header from request (framework boundary)
foreign import getRequestHeader :: APIEvent -> String -> Effect (Maybe String)

-- | Handle OPTIONS request (CORS preflight)
handleModelsOPTIONS :: APIEvent -> Aff Response
handleModelsOPTIONS _event = textResponse "" 200

-- | Handle GET request - list models
handleModelsGET :: APIEvent -> Aff Response
handleModelsGET event = do
  -- Get Omega models list
  omegaData <- liftEffect omegaDataList
  
  -- Get API key from authorization header
  authHeader <- liftEffect (getRequestHeader event "authorization")
  
  -- Get disabled models if authenticated (pure logic)
  disabledModels <- case authHeader of
    Just header -> do
      let apiKey = extractApiKey header
      case apiKey of
        Just key -> getDisabledModels key
        Nothing -> pure []
    Nothing -> pure []
  
  -- Pure operations: filter and format models
  timestamp <- liftEffect getCurrentTimestamp
  let modelIds = getModelIdsFromRecord omegaData.models
  let enabledIds = filterEnabledModels modelIds disabledModels
  let response = buildModelsResponse enabledIds timestamp
  
  -- Convert to JSON and return (framework boundary)
  jsonResponse (toJsonString response)
