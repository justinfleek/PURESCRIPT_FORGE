-- | PureScript type definitions for Forge Config types
-- | Phase 2: Type Safety Layer
module Forge.Types.Config where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Maybe (Maybe)
import Data.Argonaut (Json)
import Foreign.Object (Object)

-- | MCP server type
data McpServerType = McpLocal | McpRemote

derive instance genericMcpServerType :: Generic McpServerType _
derive instance eqMcpServerType :: Eq McpServerType

instance showMcpServerType :: Show McpServerType where
  show = genericShow

-- | MCP local configuration
type McpLocalConfig =
  { mcpType :: String
  , command :: Array String
  , enabled :: Maybe Boolean
  , timeout :: Maybe Int
  }

-- | MCP remote configuration
type McpRemoteConfig =
  { mcpType :: String
  , url :: String
  , enabled :: Maybe Boolean
  , timeout :: Maybe Int
  }

-- | MCP configuration (discriminated union)
data McpConfig
  = McpLocalCfg McpLocalConfig
  | McpRemoteCfg McpRemoteConfig

derive instance genericMcpConfig :: Generic McpConfig _
derive instance eqMcpConfig :: Eq McpConfig

instance showMcpConfig :: Show McpConfig where
  show = genericShow

-- | Permission action (config level)
data PermissionActionConfig = CfgAsk | CfgAllow | CfgDeny

derive instance genericPermissionActionConfig :: Generic PermissionActionConfig _
derive instance eqPermissionActionConfig :: Eq PermissionActionConfig

instance showPermissionActionConfig :: Show PermissionActionConfig where
  show = genericShow

-- | Agent configuration
type AgentConfig =
  { name :: String
  , prompt :: String
  , mode :: Maybe String
  }

-- | Compaction configuration
type CompactionConfig =
  { auto :: Boolean
  , prune :: Boolean
  }

-- | Configuration information (simplified)
type ConfigInfo =
  { model :: Maybe String
  , plugin :: Maybe (Array String)
  , instructions :: Maybe (Array String)
  , share :: Maybe String
  , username :: Maybe String
  , compaction :: Maybe CompactionConfig
  }
