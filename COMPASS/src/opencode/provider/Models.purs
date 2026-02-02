-- | Provider Models
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/provider/models.ts
module Opencode.Provider.Models where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

-- | Model information
type ModelInfo =
  { id :: String
  , name :: String
  , provider :: String
  , contextLength :: Int
  , maxOutputTokens :: Maybe Int
  , supportsFunctions :: Boolean
  , supportsVision :: Boolean
  , supportsStreaming :: Boolean
  }

-- | List all available models
listModels :: Aff (Either String (Array ModelInfo))
listModels = notImplemented "Provider.Models.listModels"

-- | Get models for a specific provider
getProviderModels :: String -> Aff (Either String (Array ModelInfo))
getProviderModels provider = notImplemented "Provider.Models.getProviderModels"

-- | Get model info by ID
getModel :: String -> Aff (Either String ModelInfo)
getModel modelId = notImplemented "Provider.Models.getModel"
