-- | PureScript type definitions for OpenCode Config types
-- | Phase 2: Type Safety Layer
-- | Mirrors TypeScript/Zod types from opencode-dev/packages/opencode/src/config/config.ts
module Opencode.Types.Config where

import Prelude

import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, Json, (.:), (.:?))
import Data.Argonaut.Decode.Error (JsonDecodeError(TypeMismatch))
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)
import Foreign.Object (Object)

-- | MCP server type
data McpServerType = McpLocal | McpRemote

derive instance genericMcpServerType :: Generic McpServerType _
derive instance eqMcpServerType :: Eq McpServerType

instance showMcpServerType :: Show McpServerType where
  show = genericShow

instance encodeJsonMcpServerType :: EncodeJson McpServerType where
  encodeJson = case _ of
    McpLocal -> encodeJson "local"
    McpRemote -> encodeJson "remote"

instance decodeJsonMcpServerType :: DecodeJson McpServerType where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "local" -> pure McpLocal
      "remote" -> pure McpRemote
      _ -> Left (TypeMismatch "Invalid MCP server type")

-- | MCP local configuration
type McpLocalConfig =
  { command :: Array String
  , environment :: Maybe (Object String)
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
  { url :: String
  , enabled :: Maybe Boolean
  , headers :: Maybe (Object String)
  , oauth :: Maybe (Either McpOAuthConfig Boolean)
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
data PermissionActionConfig = Ask | Allow | Deny

derive instance genericPermissionActionConfig :: Generic PermissionActionConfig _
derive instance eqPermissionActionConfig :: Eq PermissionActionConfig

instance showPermissionActionConfig :: Show PermissionActionConfig where
  show = genericShow

instance encodeJsonPermissionActionConfig :: EncodeJson PermissionActionConfig where
  encodeJson = case _ of
    Ask -> encodeJson "ask"
    Allow -> encodeJson "allow"
    Deny -> encodeJson "deny"

instance decodeJsonPermissionActionConfig :: DecodeJson PermissionActionConfig where
  decodeJson json = do
    str <- decodeJson json
    case str of
      "ask" -> pure Ask
      "allow" -> pure Allow
      "deny" -> pure Deny
      _ -> Left (TypeMismatch "Invalid permission action config")

-- | Configuration information
-- | Note: This is a simplified representation - Config.Info is very large
-- | Full type would include: provider, model, agent, mode, plugin, mcp, permission, etc.
type ConfigInfo =
  { provider :: Maybe (Object Json)
  , model :: Maybe String
  , agent :: Maybe (Object AgentConfig)
  , mode :: Maybe (Object AgentConfig)
  , plugin :: Maybe (Array String)
  , mcp :: Maybe (Object McpConfig)
  , permission :: Maybe (Object PermissionActionConfig)
  , instructions :: Maybe (Array String)
  , keybinds :: Maybe (Object String)
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
