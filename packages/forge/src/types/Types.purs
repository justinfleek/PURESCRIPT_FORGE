-- | Main module exporting all OpenCode types
-- | Phase 2: Type Safety Layer
module Opencode.Types
  ( module Opencode.Types.Session
  , module Opencode.Types.Message
  , module Opencode.Types.SessionStatus
  , module Opencode.Types.Provider
  , module Opencode.Types.Tool
  , module Opencode.Types.File
  , module Opencode.Types.State
  , module Opencode.Types.Storage
  , module Opencode.Types.Permission
  , module Opencode.Types.Config
  , SessionID
  , MessageID
  , ProviderID
  , ModelID
  , ToolID
  , PermissionID
  , ProjectID
  ) where

import Opencode.Types.Session (SessionInfo, SessionShareInfo, SessionSummary, SessionTime, RevertInfo)
import Opencode.Types.Message (MessageInfo, MessageRole(..), MessagePart, MessageMetadata, MessageTime, TokenUsage, AssistantMetadata, MessagePartType(..), MessageError(..))
import Opencode.Types.SessionStatus (SessionStatus(..), SessionStatusInfo)
import Opencode.Types.Provider (ProviderInfo, ModelInfo, ModelCapabilities, ModelCost, ModelLimits, ModelStatus(..))
import Opencode.Types.Tool (ToolInfo, ToolContext, ToolResult, ToolMetadata(..), TruncationResult(..))
import Opencode.Types.File (FilePath, FileContent, FileReadResult, CompleteFileRead(..))
import Opencode.Types.State (ProjectState, ProjectTime, UISyncState, SyncStatus(..))
import Opencode.Types.Storage (StorageKey, StorageResult(..), StorageError(..), StorageConfig)
import Opencode.Types.Permission (PermissionRule, PermissionRuleset, PermissionAction(..), PermissionRequest, PermissionReply(..), PermissionApproval)
import Opencode.Types.Config (ConfigInfo, McpConfig(..), PermissionActionConfig(..), CompactionConfig)

-- Type aliases for convenience
type SessionID = String
type MessageID = String
type ProviderID = String
type ModelID = String
type ToolID = String
type PermissionID = String
type ProjectID = String
