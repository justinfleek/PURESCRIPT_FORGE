-- | PureScript type definitions for Forge Config types
-- | Phase 2: Type Safety Layer
-- | Mirrors TypeScript/Zod types from forge-dev/packages/forge/src/config/config.ts
module Forge.Types.Config where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Maybe (Maybe)
import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, Json, (.:), (.:?))

-- | MCP server type
data McpServerType = McpLocal | McpRemote

derive instance genericMcpServerType :: Generic McpServerType _
derive instance eqMcpServerType :: Eq McpServerType

instance showMcpServerType :: Show McpServerType where
  show = genericShow

-- | MCP local configuration
type McpLocalConfig =
  { type :: String  -- "local"
  , command :: Array String
  , environment :: Maybe (Record String String)
  , enabled :: Maybe Boolean
  , timeout :: Maybe Int
  }

-- | MCP OAuth configuration
type McpOAuthConfig =
  { clientId :: Maybe String
  , clientSecret :: Maybe String
  , scope :: Maybe String
  }

-- | MCP remote configuration
type McpRemoteConfig =
  { type :: String  -- "remote"
  , url :: String
  , enabled :: Maybe Boolean
  , headers :: Maybe (Record String String)
  , oauth :: Maybe (Either McpOAuthConfig Boolean)
  , timeout :: Maybe Int
  }

-- | MCP configuration (discriminated union)
data McpConfig
  = McpLocalConfig McpLocalConfig
  | McpRemoteConfig McpRemoteConfig

derive instance genericMcpConfig :: Generic McpConfig _
derive instance eqMcpConfig :: Eq McpConfig

instance showMcpConfig :: Show McpConfig where
  show = genericShow

-- | Permission action (config level)
data PermissionActionConfig = Ask | Allow | Deny

derive instance genericPermissionActionConfig :: Generic PermissionActionConfig _
derive instance eqPermissionActionConfig :: Eq PermissionActionConfig

instance showPermissionActionConfig :: Show PermissionActionConfig where
  show = genericShow

-- | Permission object (record of permission -> action)
type PermissionObjectConfig = Record String PermissionActionConfig

-- | Configuration information
-- | Note: This is a simplified representation - Config.Info is very large
-- | Full type would include: provider, model, agent, mode, plugin, mcp, permission, etc.
type ConfigInfo =
  { provider :: Maybe (Record String Json)
  , model :: Maybe String
  , agent :: Maybe (Record String AgentConfig)
  , mode :: Maybe (Record String AgentConfig)
  , plugin :: Maybe (Array String)
  , mcp :: Maybe (Record String McpConfig)
  , permission :: Maybe PermissionObjectConfig
  , instructions :: Maybe (Array String)
  , keybinds :: Maybe (Record String String)
  , compaction :: Maybe CompactionConfig
  , share :: Maybe String
  , username :: Maybe String
  }

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

derive instance genericConfigInfo :: Generic ConfigInfo _
derive instance eqConfigInfo :: Eq ConfigInfo

instance showConfigInfo :: Show ConfigInfo where
  show = genericShow

instance encodeJsonConfigInfo :: EncodeJson ConfigInfo where
  encodeJson c = encodeJson
    { provider: c.provider
    , model: c.model
    , agent: c.agent
    , mode: c.mode
    , plugin: c.plugin
    , mcp: c.mcp
    , permission: c.permission
    , instructions: c.instructions
    , keybinds: c.keybinds
    , compaction: c.compaction
    , share: c.share
    , username: c.username
    }

instance decodeJsonConfigInfo :: DecodeJson ConfigInfo where
  decodeJson json = do
    obj <- decodeJson json
    provider <- obj .:? "provider"
    model <- obj .:? "model"
    agent <- obj .:? "agent"
    mode <- obj .:? "mode"
    plugin <- obj .:? "plugin"
    mcp <- obj .:? "mcp"
    permission <- obj .:? "permission"
    instructions <- obj .:? "instructions"
    keybinds <- obj .:? "keybinds"
    compaction <- obj .:? "compaction"
    share <- obj .:? "share"
    username <- obj .:? "username"
    pure { provider, model, agent, mode, plugin, mcp, permission, instructions, keybinds, compaction, share, username }
