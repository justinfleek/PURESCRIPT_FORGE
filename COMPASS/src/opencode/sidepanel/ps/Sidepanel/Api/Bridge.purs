-- | Bridge Server API Helpers
-- |
-- | Convenience functions for calling bridge server JSON-RPC methods.
-- | This module re-exports all bridge API functionality from sub-modules.
-- |
-- | Coeffect Equation:
-- |   Bridge : WSClient -> Method^n -> Aff (Either Error Response)^n
-- |   where each method consumes connection resources linearly
-- |
-- | Module Structure:
-- |   Bridge.Types    - All request/response type definitions
-- |   Bridge.Files    - File context and terminal operations
-- |   Bridge.Session  - Session and snapshot management
-- |   Bridge.Lean     - Lean4 proof assistant integration
-- |   Bridge.Settings - User settings persistence
module Sidepanel.Api.Bridge
  ( -- * Re-exports from Types
    module Sidepanel.Api.Bridge.Types
    -- * Re-exports from Files
  , module Sidepanel.Api.Bridge.Files
    -- * Re-exports from Session
  , module Sidepanel.Api.Bridge.Session
    -- * Re-exports from Lean
  , module Sidepanel.Api.Bridge.Lean
    -- * Re-exports from Settings
  , module Sidepanel.Api.Bridge.Settings
  ) where

-- | Type definitions for all bridge API operations
import Sidepanel.Api.Bridge.Types
  ( FileContextAddRequest
  , FileContextAddResponse
  , FileContextListRequest
  , FileContextListResponse
  , FileInContext
  , FileReadRequest
  , FileReadResponse
  , FileContextEntry
  , TerminalExecuteRequest
  , TerminalExecuteResponse
  , SessionNewRequest
  , SessionNewResponse
  , SessionState
  , SnapshotListRequest
  , SnapshotListResponse
  , SnapshotSummary
  , SnapshotSaveRequest
  , SnapshotSaveResponse
  , SnapshotRestoreRequest
  , SnapshotRestoreResponse
  , SnapshotGetRequest
  , SnapshotGetResponse
  , SnapshotGetState
  , BalanceState
  , ProofState
  , UsageMetrics
  , LeanCheckRequest
  , LeanCheckResponse
  , LeanDiagnostic
  , LeanGoalsRequest
  , LeanGoalsResponse
  , LeanGoal
  , LeanApplyTacticRequest
  , LeanApplyTacticResponse
  , LeanSearchTheoremsRequest
  , LeanSearchTheoremsResponse
  , TheoremResult
  , SettingsSaveRequest
  , SettingsSaveResponse
  )

-- | File context, terminal, and file read operations
import Sidepanel.Api.Bridge.Files
  ( addFileToContext
  , listFilesInContext
  , readFileContent
  , executeTerminalCommand
  )

-- | Session and snapshot operations
import Sidepanel.Api.Bridge.Session
  ( createNewSession
  , listSnapshots
  , saveSnapshot
  , restoreSnapshot
  , getSnapshot
  )

-- | Lean4 proof assistant operations
import Sidepanel.Api.Bridge.Lean
  ( checkLeanFile
  , getLeanGoals
  , applyLeanTactic
  , searchLeanTheorems
  )

-- | Settings persistence operations
import Sidepanel.Api.Bridge.Settings
  ( saveSettings
  )
