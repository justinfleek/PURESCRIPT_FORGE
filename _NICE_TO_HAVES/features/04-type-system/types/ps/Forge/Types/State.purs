-- | PureScript type definitions for Forge State types
-- | Phase 2: Type Safety Layer
-- | Mirrors TypeScript types from forge-dev/packages/forge/src/project/state.ts and UI state
module Forge.Types.State where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Maybe (Maybe)
import Data.Argonaut (class EncodeJson, class DecodeJson, encodeJson, decodeJson, Json, (.:), (.:?))
import Effect.Aff (Aff)
import Forge.Types.Session (SessionInfo)
import Forge.Types.Message (MessageInfo)
import Forge.Types.SessionStatus (SessionStatus)
import Forge.Types.Provider (ProviderInfo)
import Forge.Types.Permission (PermissionRequest)
import Forge.Types.Config (ConfigInfo)

-- | State entry with disposal
type StateEntry state =
  { state :: state
  , dispose :: Maybe (state -> Aff Unit)
  }

-- | State management operations
-- | Note: This is a simplified representation - actual implementation uses Map-based state
class StateManager m where
  createState :: forall s. (Unit -> String) -> (Unit -> s) -> Maybe (s -> Aff Unit) -> m (Unit -> s)
  disposeState :: String -> Aff Unit

-- | Project state information
type ProjectState =
  { id :: String
  , worktree :: String
  , vcs :: Maybe String  -- "git" or Nothing
  , name :: Maybe String
  , time :: ProjectTime
  , sandboxes :: Array String
  }

-- | Project time information
type ProjectTime =
  { created :: Number
  , updated :: Number
  , initialized :: Maybe Number
  }

derive instance genericProjectState :: Generic ProjectState _
derive instance eqProjectState :: Eq ProjectState

instance showProjectState :: Show ProjectState where
  show = genericShow

-- | UI sync state (from TUI context)
type UISyncState =
  { status :: SyncStatus
  , provider :: Array ProviderInfo  -- Would import from Provider module
  , provider_default :: Record String String
  , provider_next :: ProviderListResponse
  , provider_auth :: Record String (Array ProviderAuthMethod)
  , agent :: Array AgentInfo
  , command :: Array CommandInfo
  , permission :: Record String (Array PermissionRequest)
  , question :: Record String (Array QuestionRequest)
  , config :: ConfigInfo
  , session :: Array SessionInfo
  , session_status :: Record String SessionStatus
  , session_diff :: Record String (Array FileDiff)
  , todo :: Record String (Array TodoInfo)
  , message :: Record String (Array MessageInfo)
  , part :: Record String (Array PartInfo)
  , lsp :: Array LspStatus
  , mcp :: Record String McpStatus
  , mcp_resource :: Record String McpResource
  , formatter :: Array FormatterStatus
  , vcs :: Maybe VcsInfo
  , path :: PathInfo
  }

-- | Sync status
data SyncStatus = Loading | Partial | Complete

derive instance genericSyncStatus :: Generic SyncStatus _
derive instance eqSyncStatus :: Eq SyncStatus

instance showSyncStatus :: Show SyncStatus where
  show = genericShow

-- | Placeholder types (would import from respective modules)
type ProviderInfo = { id :: String, name :: String }
type ProviderListResponse = { all :: Array ProviderInfo, default :: Record String String, connected :: Array String }
type ProviderAuthMethod = { type :: String, url :: Maybe String }
type AgentInfo = { id :: String, name :: String }
type CommandInfo = { id :: String, name :: String }
type PermissionRequest = { id :: String, permission :: String, patterns :: Array String }
type QuestionRequest = { id :: String, question :: String }
type ConfigInfo = Record String Json
type FileDiff = { path :: String, additions :: Int, deletions :: Int }
type TodoInfo = { id :: String, content :: String, status :: String }
type PartInfo = { id :: String, type :: String, content :: String }
type LspStatus = { id :: String, status :: String }
type McpStatus = { id :: String, status :: String }
type McpResource = { id :: String, uri :: String }
type FormatterStatus = { id :: String, status :: String }
type VcsInfo = { type :: String, branch :: Maybe String }
type PathInfo = { state :: String, config :: String, worktree :: String, directory :: String }

derive instance genericUISyncState :: Generic UISyncState _
derive instance eqUISyncState :: Eq UISyncState

instance showUISyncState :: Show UISyncState where
  show = genericShow
