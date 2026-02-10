-- | PureScript type definitions for OpenCode State types
-- | Phase 2: Type Safety Layer
-- | Mirrors TypeScript types from opencode-dev/packages/opencode/src/project/state.ts and UI state
module Opencode.Types.State where

import Prelude

import Data.Argonaut (Json)
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe)
import Data.Show.Generic (genericShow)
import Effect.Aff (Aff)
import Foreign.Object (Object)
import Opencode.Types.Config (ConfigInfo)
import Opencode.Types.Message (MessageInfo)
import Opencode.Types.Permission (PermissionRequest)
import Opencode.Types.Provider (ProviderInfo)
import Opencode.Types.Session (SessionInfo)
import Opencode.Types.SessionStatus (SessionStatus)

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
  , vcs :: Maybe String
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

-- | Sync status
data SyncStatus = Loading | Partial | Complete

derive instance genericSyncStatus :: Generic SyncStatus _
derive instance eqSyncStatus :: Eq SyncStatus

instance showSyncStatus :: Show SyncStatus where
  show = genericShow

-- | Provider list response
type ProviderListResponse =
  { all :: Array ProviderInfo
  , default :: Object String
  , connected :: Array String
  }

-- | Provider auth method
type ProviderAuthMethod =
  { authType :: String
  , url :: Maybe String
  }

-- | Agent info (UI-level)
type AgentInfo = { id :: String, name :: String }

-- | Command info
type CommandInfo = { id :: String, name :: String }

-- | Question request
type QuestionRequest = { id :: String, question :: String }

-- | Todo info
type TodoInfo = { id :: String, content :: String, status :: String }

-- | Part info
type PartInfo = { id :: String, partType :: String, content :: String }

-- | LSP status
type LspStatus = { id :: String, status :: String }

-- | MCP status
type McpStatus = { id :: String, status :: String }

-- | MCP resource
type McpResource = { id :: String, uri :: String }

-- | Formatter status
type FormatterStatus = { id :: String, status :: String }

-- | VCS info
type VcsInfo = { vcsType :: String, branch :: Maybe String }

-- | Path info (state-level)
type StatePathInfo =
  { state :: String
  , config :: String
  , worktree :: String
  , directory :: String
  }

-- | File diff (state-level)
type FileDiff = { path :: String, additions :: Int, deletions :: Int }

-- | UI sync state (from TUI context)
type UISyncState =
  { status :: SyncStatus
  , provider :: Array ProviderInfo
  , providerDefault :: Object String
  , providerNext :: ProviderListResponse
  , providerAuth :: Object (Array ProviderAuthMethod)
  , agent :: Array AgentInfo
  , command :: Array CommandInfo
  , permission :: Object (Array PermissionRequest)
  , question :: Object (Array QuestionRequest)
  , config :: ConfigInfo
  , session :: Array SessionInfo
  , sessionStatus :: Object SessionStatus
  , sessionDiff :: Object (Array FileDiff)
  , todo :: Object (Array TodoInfo)
  , message :: Object (Array MessageInfo)
  , part :: Object (Array PartInfo)
  , lsp :: Array LspStatus
  , mcp :: Object McpStatus
  , mcpResource :: Object McpResource
  , formatter :: Array FormatterStatus
  , vcs :: Maybe VcsInfo
  , path :: StatePathInfo
  }
