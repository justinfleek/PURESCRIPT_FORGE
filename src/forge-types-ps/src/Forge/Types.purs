-- | Main module exporting all Forge types
-- | Phase 2: Type Safety Layer
-- | Use qualified imports to avoid naming conflicts
module Forge.Types 
  ( module Forge.Types.Session
  , module Forge.Types.Message
  , module Forge.Types.SessionStatus
  , module Forge.Types.Provider
  , module Forge.Types.File
  , module Forge.Types.State
  , module Forge.Types.Storage
  , module Forge.Types.Permission
  , module Forge.Types.Config
  -- Tool module has conflicting SessionID, import separately
  ) where

import Forge.Types.Session (SessionID, ProjectID, FileDiff, SessionSummary, ShareInfo, SessionTime, RevertInfo, SessionInfo, SessionShareInfo)
import Forge.Types.Message (MessageRole(..), MessagePartType(..), MessagePart, MessageTime, TokenUsage, AssistantMetadata, ToolMetadata, MessageError(..), MessageMetadata, MessageInfo)
import Forge.Types.SessionStatus (SessionStatus(..), SessionStatusInfo)
import Forge.Types.Provider (ProviderID, ModelID, ApiInfo, InputCapabilities, OutputCapabilities, ModelCapabilities, CacheCost, ModelCost, ModelLimits, ModelStatus(..), ModelInfo, ProviderInfo)
import Forge.Types.File (FilePath, DirectoryPath, FileContent, FileReadResult, FileExists, IsDirectory, CompleteFileRead(..), BannedFileOperation(..))
import Forge.Types.State (ProjectState, ProjectTime, SyncStatus(..), UISyncState)
import Forge.Types.Storage (StorageKey, StorageResult(..), StorageErrorType(..), StorageConfig)
import Forge.Types.Permission (PermissionID, PermissionAction(..), PermissionRule, PermissionRuleset, ToolInfo, PermissionRequest, PermissionReply(..), PermissionApproval)
import Forge.Types.Config (McpServerType(..), McpLocalConfig, McpRemoteConfig, McpConfig(..), PermissionActionConfig(..), AgentConfig, CompactionConfig, ConfigInfo)
