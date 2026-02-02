-- | PureScript type definitions for OpenCode Provider types
-- | Phase 2: Type Safety Layer
module Opencode.Types.Provider where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Maybe (Maybe)
import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, Json, (.:), (.:?))

-- | Provider identifier
type ProviderID = String

-- | Model identifier
type ModelID = String

-- | API information
type ApiInfo =
  { id :: String
  , url :: String
  , npm :: String
  }

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
  , inputText :: Boolean
  , inputImage :: Boolean
  , outputText :: Boolean
  }

-- | Cache cost
type CacheCost =
  { read :: Number
  , write :: Number
  }

-- | Model cost information
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

-- | Model status
data ModelStatus = Alpha | Beta | Deprecated | Active

derive instance genericModelStatus :: Generic ModelStatus _
derive instance eqModelStatus :: Eq ModelStatus

instance showModelStatus :: Show ModelStatus where
  show = genericShow

-- | Model information
type ModelInfo =
  { id :: ModelID
  , providerID :: ProviderID
  , name :: String
  , family :: Maybe String
  , capabilities :: ModelCapabilities
  , cost :: ModelCost
  , limit :: ModelLimits
  , status :: ModelStatus
  }

-- | Provider information
type ProviderInfo =
  { id :: ProviderID
  , name :: String
  }

-- Note: PureScript uses automatic record encoding from Argonaut
