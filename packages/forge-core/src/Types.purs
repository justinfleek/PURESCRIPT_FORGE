-- | Main module exporting all Forge types
-- | Phase 2: Type Safety Layer
module Forge.Types where

-- Re-export all type modules
import Forge.Types.Session (SessionInfo, SessionShareInfo, SessionSummary, SessionTime, RevertInfo)
import Forge.Types.Message (MessageInfo, MessageRole, MessagePart, MessageMetadata, MessageTime, TokenUsage, AssistantMetadata)
import Forge.Types.SessionStatus (SessionStatus(..), SessionStatusInfo)
import Forge.Types.Provider (ProviderInfo, ModelInfo, ModelCapabilities, ModelCost, ModelLimits, ModelStatus(..))
import Forge.Types.Tool (ToolInfo, ToolContext, ToolResult, ToolMetadata, TruncationResult(..))
import Forge.Types.File (FilePath, FileContent, FileReadResult, CompleteFileRead(..))
import Forge.Types.State (ProjectState, ProjectTime, UISyncState, SyncStatus(..))
import Forge.Types.Storage (StorageKey, StorageResult(..), StorageError(..), StorageConfig)
import Forge.Types.Permission (PermissionRule, PermissionRuleset, PermissionAction(..), PermissionRequest, PermissionReply(..), PermissionApproval)
import Forge.Types.Config (ConfigInfo, McpConfig(..), PermissionActionConfig(..), CompactionConfig)

-- Type aliases for convenience
type SessionID = String
type MessageID = String
type ProviderID = String
type ModelID = String
type ToolID = String
type PermissionID = String
type ProjectID = String
