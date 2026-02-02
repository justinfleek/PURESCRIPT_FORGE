-- | Main module exporting all OpenCode types
-- | Phase 2: Type Safety Layer
-- | Use qualified imports to avoid naming conflicts
module Opencode.Types 
  ( module Opencode.Types.Session
  , module Opencode.Types.Message
  , module Opencode.Types.SessionStatus
  , module Opencode.Types.Provider
  , module Opencode.Types.File
  , module Opencode.Types.State
  , module Opencode.Types.Storage
  , module Opencode.Types.Permission
  , module Opencode.Types.Config
  -- Tool module has conflicting SessionID, import separately
  ) where

import Opencode.Types.Session (SessionID, ProjectID, FileDiff, SessionSummary, ShareInfo, SessionTime, RevertInfo, SessionInfo, SessionShareInfo)
import Opencode.Types.Message (MessageRole(..), MessagePartType(..), MessagePart, MessageTime, TokenUsage, AssistantMetadata, ToolMetadata, MessageError(..), MessageMetadata, MessageInfo)
import Opencode.Types.SessionStatus (SessionStatus(..), SessionStatusInfo)
import Opencode.Types.Provider (ProviderID, ModelID, ApiInfo, InputCapabilities, OutputCapabilities, ModelCapabilities, CacheCost, ModelCost, ModelLimits, ModelStatus(..), ModelInfo, ProviderInfo)
import Opencode.Types.File (FilePath, DirectoryPath, FileContent, FileReadResult, FileExists, IsDirectory, CompleteFileRead(..), BannedFileOperation(..))
import Opencode.Types.State (ProjectState, ProjectTime, SyncStatus(..), UISyncState)
import Opencode.Types.Storage (StorageKey, StorageResult(..), StorageErrorType(..), StorageConfig)
import Opencode.Types.Permission (PermissionID, PermissionAction(..), PermissionRule, PermissionRuleset, ToolInfo, PermissionRequest, PermissionReply(..), PermissionApproval)
import Opencode.Types.Config (McpServerType(..), McpLocalConfig, McpRemoteConfig, McpConfig(..), PermissionActionConfig(..), AgentConfig, CompactionConfig, ConfigInfo)
