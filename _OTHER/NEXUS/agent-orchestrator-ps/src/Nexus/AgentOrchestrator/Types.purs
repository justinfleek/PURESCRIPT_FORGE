module Nexus.AgentOrchestrator.Types where

import Prelude

import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, (.:), (.:?))
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))

-- | Agent type
data AgentType = WebSearch | ContentExtraction | NetworkFormation | DatabaseLayer

derive instance eqAgentType :: Eq AgentType
derive instance ordAgentType :: Ord AgentType

instance showAgentType :: Show AgentType where
  show WebSearch = "web_search"
  show ContentExtraction = "content_extraction"
  show NetworkFormation = "network_formation"
  show DatabaseLayer = "database_layer"

instance encodeJsonAgentType :: EncodeJson AgentType where
  encodeJson = encodeJson <<< show

instance decodeJsonAgentType :: DecodeJson AgentType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "web_search" -> pure WebSearch
      "content_extraction" -> pure ContentExtraction
      "network_formation" -> pure NetworkFormation
      "database_layer" -> pure DatabaseLayer
      _ -> Left "Invalid agent type"

-- | Agent status
data AgentStatus = Running | Stopped | Error

derive instance eqAgentStatus :: Eq AgentStatus
derive instance ordAgentStatus :: Ord AgentStatus

instance showAgentStatus :: Show AgentStatus where
  show Running = "running"
  show Stopped = "stopped"
  show Error = "error"

instance encodeJsonAgentStatus :: EncodeJson AgentStatus where
  encodeJson = encodeJson <<< show

instance decodeJsonAgentStatus :: DecodeJson AgentStatus where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "running" -> pure Running
      "stopped" -> pure Stopped
      "error" -> pure Error
      _ -> Left "Invalid agent status"

-- | Agent configuration
type AgentConfig =
  { initialQuery :: Maybe String
  , maxResults :: Int
  , timeoutSeconds :: Int
  }

instance encodeJsonAgentConfig :: EncodeJson AgentConfig where
  encodeJson c = encodeJson
    { initialQuery: c.initialQuery
    , maxResults: c.maxResults
    , timeoutSeconds: c.timeoutSeconds
    }

instance decodeJsonAgentConfig :: DecodeJson AgentConfig where
  decodeJson json = do
    obj <- decodeJson json
    initialQuery <- obj .:? "initialQuery"
    maxResults <- obj .: "maxResults"
    timeoutSeconds <- obj .: "timeoutSeconds"
    pure { initialQuery, maxResults, timeoutSeconds }

-- | Agent record
type AgentRecord =
  { agentId :: String
  , agentType :: AgentType
  , config :: AgentConfig
  , status :: AgentStatus
  , startedAt :: String
  , updatedAt :: String
  , processId :: Maybe Int
  }

instance encodeJsonAgentRecord :: EncodeJson AgentRecord where
  encodeJson a = encodeJson
    { agentId: a.agentId
    , agentType: a.agentType
    , config: a.config
    , status: a.status
    , startedAt: a.startedAt
    , updatedAt: a.updatedAt
    , processId: a.processId
    }

instance decodeJsonAgentRecord :: DecodeJson AgentRecord where
  decodeJson json = do
    obj <- decodeJson json
    agentId <- obj .: "agentId"
    agentType <- obj .: "agentType"
    config <- obj .: "config"
    status <- obj .: "status"
    startedAt <- obj .: "startedAt"
    updatedAt <- obj .: "updatedAt"
    processId <- obj .:? "processId"
    pure { agentId, agentType, config, status, startedAt, updatedAt, processId }

-- | Sandbox configuration
type SandboxConfig =
  { allowedDirs :: Array { hostPath :: String, sandboxPath :: String, readOnly :: Boolean }
  , networkAccess :: Boolean
  , workingDir :: String
  }

instance encodeJsonSandboxConfig :: EncodeJson SandboxConfig where
  encodeJson s = encodeJson
    { allowedDirs: s.allowedDirs
    , networkAccess: s.networkAccess
    , workingDir: s.workingDir
    }

instance decodeJsonSandboxConfig :: DecodeJson SandboxConfig where
  decodeJson json = do
    obj <- decodeJson json
    allowedDirs <- obj .: "allowedDirs"
    networkAccess <- obj .: "networkAccess"
    workingDir <- obj .: "workingDir"
    pure { allowedDirs, networkAccess, workingDir }
