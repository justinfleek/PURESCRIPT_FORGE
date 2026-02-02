-- | PureScript type definitions for OpenCode Provider types
-- | Phase 2: Type Safety Layer
-- | Mirrors TypeScript/Zod types from opencode-dev/packages/opencode/src/provider/
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

-- | Model capabilities
type ModelCapabilities =
  { temperature :: Boolean
  , reasoning :: Boolean
  , attachment :: Boolean
  , toolcall :: Boolean
  , input :: InputCapabilities
  , output :: OutputCapabilities
  , interleaved :: InterleavedCapability
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

-- | Interleaved capability (boolean or object)
data InterleavedCapability
  = InterleavedBoolean Boolean
  | InterleavedObject { field :: String }  -- "reasoning_content" | "reasoning_details"

derive instance genericInterleavedCapability :: Generic InterleavedCapability _
derive instance eqInterleavedCapability :: Eq InterleavedCapability

instance showInterleavedCapability :: Show InterleavedCapability where
  show = genericShow

-- | Model cost information
type ModelCost =
  { input :: Number
  , output :: Number
  , cache :: CacheCost
  , experimentalOver200K :: Maybe ExperimentalCost
  }

-- | Cache cost
type CacheCost =
  { read :: Number
  , write :: Number
  }

-- | Experimental cost (over 200K tokens)
type ExperimentalCost =
  { input :: Number
  , output :: Number
  , cache :: CacheCost
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
  , api :: ApiInfo
  , name :: String
  , family :: Maybe String
  , capabilities :: ModelCapabilities
  , cost :: ModelCost
  , limit :: ModelLimits
  , status :: ModelStatus
  , options :: Record String Json  -- z.record(z.string(), z.any())
  , headers :: Record String String
  , release_date :: String
  , variants :: Maybe (Record String (Record String Json))
  }

derive instance genericModelInfo :: Generic ModelInfo _
derive instance eqModelInfo :: Eq ModelInfo

instance showModelInfo :: Show ModelInfo where
  show = genericShow

-- | Provider information
type ProviderInfo =
  { id :: ProviderID
  , name :: String
  }

derive instance genericProviderInfo :: Generic ProviderInfo _
derive instance eqProviderInfo :: Eq ProviderInfo

instance showProviderInfo :: Show ProviderInfo where
  show = genericShow

instance encodeJsonProviderInfo :: EncodeJson ProviderInfo where
  encodeJson p = encodeJson { id: p.id, name: p.name }

instance decodeJsonProviderInfo :: DecodeJson ProviderInfo where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    name <- obj .: "name"
    pure { id, name }
