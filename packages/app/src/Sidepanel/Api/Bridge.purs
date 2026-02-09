-- | Bridge Server API Helpers
-- | Convenience functions for calling bridge server JSON-RPC methods
module Sidepanel.Api.Bridge where

import Prelude
import Effect.Aff (Aff, throwError)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Exception (error)
import Sidepanel.WebSocket.Client (WSClient, request)
import Sidepanel.Api.Types (JsonRpcError)
import Data.Argonaut.Core (Json)
import Data.Argonaut.Decode (decodeJson)
import Data.Argonaut.Encode (encodeJson)

-- | Bridge-local session type (uses String for timestamps to enable JSON decoding)
type BridgeSessionState =
  { id :: String
  , model :: String
  , promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  , cost :: Number
  , messageCount :: Int
  , startedAt :: String  -- ISO 8601
  }

-- | File context add request
type FileContextAddRequest =
  { path :: String
  , sessionId :: Maybe String
  }

-- | File context add response
type FileContextAddResponse =
  { success :: Boolean
  , tokens :: Int
  , contextBudget ::
      { used :: Int
      , total :: Int
      }
  }

-- | File context list request
type FileContextListRequest =
  { sessionId :: Maybe String
  , filter :: Maybe String
  }

-- | File in context
type FileInContext =
  { path :: String
  , tokens :: Int
  , readAt :: Number
  , status :: String
  , language :: String
  , size :: Int
  }

-- | File context list response
type FileContextListResponse =
  { files :: Array FileInContext
  , contextBudget ::
      { used :: Int
      , total :: Int
      }
  }

-- | Terminal execute request
type TerminalExecuteRequest =
  { command :: String
  , cwd :: Maybe String
  , sessionId :: Maybe String
  }

-- | Terminal execute response
type TerminalExecuteResponse =
  { success :: Boolean
  , output :: Maybe String
  , exitCode :: Maybe Int
  }

-- | Session new request
type SessionNewRequest =
  { name :: Maybe String
  , parentId :: Maybe String
  , model :: Maybe String
  , provider :: Maybe String
  }

-- | Session new response
type SessionNewResponse =
  { sessionId :: String
  , success :: Boolean
  }

-- | Add file to context
addFileToContext :: WSClient -> FileContextAddRequest -> Aff (Either JsonRpcError FileContextAddResponse)
addFileToContext client req =
  request client "file.context.add" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff FileContextAddResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | List files in context
listFilesInContext :: WSClient -> FileContextListRequest -> Aff (Either JsonRpcError FileContextListResponse)
listFilesInContext client req =
  request client "file.context.list" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff FileContextListResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | Execute terminal command
executeTerminalCommand :: WSClient -> TerminalExecuteRequest -> Aff (Either JsonRpcError TerminalExecuteResponse)
executeTerminalCommand client req =
  request client "terminal.execute" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff TerminalExecuteResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | Create new session
createNewSession :: WSClient -> SessionNewRequest -> Aff (Either JsonRpcError SessionNewResponse)
createNewSession client req =
  request client "session.new" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff SessionNewResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | File read request
type FileReadRequest =
  { path :: String
  }

-- | File read response
type FileReadResponse =
  { success :: Boolean
  , content :: Maybe String
  , error :: Maybe String
  }

-- | Read file content
readFileContent :: WSClient -> FileReadRequest -> Aff (Either JsonRpcError FileReadResponse)
readFileContent client req =
  request client "file.read" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff FileReadResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | Snapshot list request
type SnapshotListRequest =
  { limit :: Maybe Int
  , offset :: Maybe Int
  }

-- | Snapshot summary
type SnapshotSummary =
  { id :: String
  , timestamp :: String  -- ISO 8601 string
  , description :: Maybe String
  }

-- | Snapshot list response
type SnapshotListResponse =
  { snapshots :: Array SnapshotSummary
  }

-- | Snapshot save request
type SnapshotSaveRequest =
  { trigger :: String
  , description :: Maybe String
  }

-- | Snapshot save response
type SnapshotSaveResponse =
  { id :: String
  , success :: Boolean
  }

-- | Snapshot restore request
type SnapshotRestoreRequest =
  { id :: String
  }

-- | Snapshot restore response
type SnapshotRestoreResponse =
  { success :: Boolean
  }

-- | List snapshots
listSnapshots :: WSClient -> SnapshotListRequest -> Aff (Either JsonRpcError SnapshotListResponse)
listSnapshots client req =
  request client "snapshot.list" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff SnapshotListResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | Save snapshot
saveSnapshot :: WSClient -> SnapshotSaveRequest -> Aff (Either JsonRpcError SnapshotSaveResponse)
saveSnapshot client req =
  request client "snapshot.save" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff SnapshotSaveResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | Restore snapshot
restoreSnapshot :: WSClient -> SnapshotRestoreRequest -> Aff (Either JsonRpcError SnapshotRestoreResponse)
restoreSnapshot client req =
  request client "snapshot.restore" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff SnapshotRestoreResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | Snapshot get request
type SnapshotGetRequest =
  { id :: String
  }

-- | Snapshot get response
type SnapshotGetResponse =
  { id :: String
  , timestamp :: String
  , description :: Maybe String
  , state :: SnapshotGetState
  }

type SnapshotGetState =
  { balance :: Maybe BalanceState
  , session :: Maybe BridgeSessionState
  , proof :: Maybe ProofState
  , metrics :: Maybe UsageMetrics
  , fileContext :: Array FileContextEntry
  }

type FileContextEntry =
  { path :: String
  , tokens :: Int
  , language :: String
  }

type BalanceState =
  { venice :: { diem :: Number, usd :: Number, effective :: Number, lastUpdated :: Maybe String }
  , consumptionRate :: Number
  , timeToDepletion :: Maybe Int
  , todayUsed :: Number
  , todayStartBalance :: Number
  , resetCountdown :: Maybe Int
  , alertLevel :: String
  }

type ProofState =
  { connected :: Boolean
  , file :: Maybe String
  , position :: Maybe { line :: Int, col :: Int }
  , goals :: Array { type_ :: String, context :: Array { name :: String, type_ :: String } }
  , diagnostics :: Array { severity :: String, message :: String, range :: { start :: { line :: Int, col :: Int }, end :: { line :: Int, col :: Int } } }
  , suggestedTactics :: Array { name :: String, description :: String, confidence :: Number }
  }

type UsageMetrics =
  { totalTokens :: Int
  , totalCost :: Number
  , averageResponseTime :: Number
  , toolTimings :: Array { name :: String, duration :: Number }
  }

-- | Get snapshot by ID
getSnapshot :: WSClient -> SnapshotGetRequest -> Aff (Either JsonRpcError SnapshotGetResponse)
getSnapshot client req =
  request client "snapshot.get" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff SnapshotGetResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | Lean check request
type LeanCheckRequest =
  { file :: String
  }

-- | Lean diagnostic
type LeanDiagnostic =
  { severity :: String
  , message :: String
  , range ::
      { start :: { line :: Int, col :: Int }
      , end :: { line :: Int, col :: Int }
      }
  }

-- | Lean check response
type LeanCheckResponse =
  { diagnostics :: Array LeanDiagnostic
  }

-- | Lean goals request
type LeanGoalsRequest =
  { file :: String
  , line :: Int
  , column :: Int
  }

-- | Lean goal
type LeanGoal =
  { type_ :: String
  , context :: Array { name :: String, type_ :: String }
  }

-- | Lean goals response
type LeanGoalsResponse =
  { goals :: Array LeanGoal
  }

-- | Check Lean file
checkLeanFile :: WSClient -> LeanCheckRequest -> Aff (Either JsonRpcError LeanCheckResponse)
checkLeanFile client req =
  request client "lean.check" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff LeanCheckResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | Get Lean goals
getLeanGoals :: WSClient -> LeanGoalsRequest -> Aff (Either JsonRpcError LeanGoalsResponse)
getLeanGoals client req =
  request client "lean.goals" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff LeanGoalsResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | Apply Lean tactic request
type LeanApplyTacticRequest =
  { file :: String
  , line :: Int
  , column :: Int
  , tactic :: String
  , goalIndex :: Maybe Int
  }

-- | Apply Lean tactic response
type LeanApplyTacticResponse =
  { success :: Boolean
  , message :: Maybe String
  , goals :: Array LeanGoal
  }

-- | Apply Lean tactic
applyLeanTactic :: WSClient -> LeanApplyTacticRequest -> Aff (Either JsonRpcError LeanApplyTacticResponse)
applyLeanTactic client req =
  request client "lean.applyTactic" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff LeanApplyTacticResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | Search Lean theorems request
type LeanSearchTheoremsRequest =
  { query :: String
  , limit :: Maybe Int
  , file :: Maybe String
  }

-- | Theorem search result
type TheoremResult =
  { name :: String
  , statement :: String
  , file :: String
  , line :: Int
  , description :: Maybe String
  }

-- | Search Lean theorems response
type LeanSearchTheoremsResponse =
  { theorems :: Array TheoremResult
  , total :: Int
  }

-- | Search Lean theorems
searchLeanTheorems :: WSClient -> LeanSearchTheoremsRequest -> Aff (Either JsonRpcError LeanSearchTheoremsResponse)
searchLeanTheorems client req =
  request client "lean.searchTheorems" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff LeanSearchTheoremsResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | Settings save request (matches Settings type from Sidepanel.State.Settings)
type SettingsSaveRequest =
  { alerts ::
      { warningPercent :: Number
      , criticalPercent :: Number
      , warningHours :: Number
      , soundEnabled :: Boolean
      }
  , appearance ::
      { theme :: String
      }
  , keyboard ::
      { enabled :: Boolean
      , vimMode :: Boolean
      }
  , features ::
      { countdown :: Boolean
      , tokenCharts :: Boolean
      , proofPanel :: Boolean
      , timeline :: Boolean
      }
  , storage ::
      { retentionDays :: Int
      }
  }

-- | Settings save response
type SettingsSaveResponse =
  { success :: Boolean
  }

-- | Save settings to bridge server
saveSettings :: WSClient -> SettingsSaveRequest -> Aff (Either JsonRpcError SettingsSaveResponse)
saveSettings client req =
  request client "settings.save" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff SettingsSaveResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | State get request (empty params)
type StateGetRequest = {}

-- | Full state response
type StateGetResponse =
  { connected :: Boolean
  , balance :: Maybe BalanceState
  , session :: Maybe BridgeSessionState
  , proof :: Maybe ProofState
  , metrics :: Maybe UsageMetrics
  , snapshots :: Array SnapshotSummary
  , timestamp :: String  -- ISO 8601
  }

-- | Get full state from bridge server
getState :: WSClient -> StateGetRequest -> Aff (Either JsonRpcError StateGetResponse)
getState client req =
  request client "state.get" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff StateGetResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | State subscribe request
type StateSubscribeRequest =
  { paths :: Maybe (Array String)  -- Optional: subscribe to specific paths only
  }

-- | State subscribe response
type StateSubscribeResponse =
  { subscribed :: Boolean
  , paths :: Array String  -- Confirmed subscribed paths
  }

-- | Subscribe to state updates
subscribeState :: WSClient -> StateSubscribeRequest -> Aff (Either JsonRpcError StateSubscribeResponse)
subscribeState client req =
  request client "state.subscribe" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff StateSubscribeResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | Alerts configure request
type AlertsConfigureRequest =
  { diemWarningPercent :: Maybe Number
  , diemCriticalPercent :: Maybe Number
  , depletionWarningHours :: Maybe Number
  }

-- | Alerts configure response
type AlertsConfigureResponse =
  { success :: Boolean
  }

-- | Configure alert thresholds
configureAlerts :: WSClient -> AlertsConfigureRequest -> Aff (Either JsonRpcError AlertsConfigureResponse)
configureAlerts client req =
  request client "alerts.configure" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff AlertsConfigureResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | Session export request
type SessionExportRequest =
  { sessionId :: String
  , format :: String  -- "json" | "markdown" | "html"
  , includeTimeline :: Maybe Boolean
  }

-- | Session export response
type SessionExportResponse =
  { exportData :: String  -- Exported data (JSON string, Markdown, or HTML)
  , filename :: String
  }

-- | Export session data
exportSession :: WSClient -> SessionExportRequest -> Aff (Either JsonRpcError SessionExportResponse)
exportSession client req =
  request client "session.export" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff SessionExportResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | File context remove request
type FileContextRemoveRequest =
  { paths :: Array String
  , sessionId :: Maybe String
  }

-- | File context remove response
type FileContextRemoveResponse =
  { success :: Boolean
  , removedCount :: Int
  , contextBudget ::
      { used :: Int
      , total :: Int
      }
  }

-- | Remove files from context
removeFileFromContext :: WSClient -> FileContextRemoveRequest -> Aff (Either JsonRpcError FileContextRemoveResponse)
removeFileFromContext client req =
  request client "file.context.remove" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff FileContextRemoveResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | Diff accept hunk request
type DiffAcceptHunkRequest =
  { file :: String
  , hunkId :: String
  }

-- | Diff accept hunk response
type DiffAcceptHunkResponse =
  { success :: Boolean
  }

-- | Accept a diff hunk
acceptDiffHunk :: WSClient -> DiffAcceptHunkRequest -> Aff (Either JsonRpcError DiffAcceptHunkResponse)
acceptDiffHunk client req =
  request client "diff.hunk.accept" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff DiffAcceptHunkResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | Reject a diff hunk
rejectDiffHunk :: WSClient -> DiffAcceptHunkRequest -> Aff (Either JsonRpcError DiffAcceptHunkResponse)
rejectDiffHunk client req =
  request client "diff.hunk.reject" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff DiffAcceptHunkResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | Diff accept all request (file or global)
type DiffAcceptAllRequest =
  { file :: Maybe String  -- Nothing = all files
  }

-- | Accept all diff hunks
acceptAllDiffHunks :: WSClient -> DiffAcceptAllRequest -> Aff (Either JsonRpcError DiffAcceptHunkResponse)
acceptAllDiffHunks client req =
  request client "diff.accept.all" (encodeJson { file: req.file }) decodeResponse
  where
    decodeResponse :: Json -> Aff DiffAcceptHunkResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | Reject all diff hunks
rejectAllDiffHunks :: WSClient -> DiffAcceptAllRequest -> Aff (Either JsonRpcError DiffAcceptHunkResponse)
rejectAllDiffHunks client req =
  request client "diff.reject.all" (encodeJson { file: req.file }) decodeResponse
  where
    decodeResponse :: Json -> Aff DiffAcceptHunkResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | Performance data request
type PerformanceDataRequest =
  { sessionId :: String
  }

-- | Performance data response
type PerformanceDataResponse =
  { sessionId :: String
  , totalDuration :: Number
  , aiThinkingTime :: Number
  , toolExecutionTime :: Number
  , networkTime :: Number
  , totalTokens :: Int
  , totalCost :: Number
  , messageCount :: Int
  , toolCallCount :: Int
  , events :: Json  -- Complex nested structure, decode client-side
  , slowestOperations :: Json
  , suggestions :: Json
  }

-- | Get performance data for a session
getPerformanceData :: WSClient -> PerformanceDataRequest -> Aff (Either JsonRpcError PerformanceDataResponse)
getPerformanceData client req =
  request client "performance.data" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff PerformanceDataResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result

-- | Search request
type SearchRequest =
  { query :: String
  , types :: Maybe (Array String)  -- Optional: filter by result types
  , dateRange :: Maybe { start :: Maybe String, end :: Maybe String }  -- ISO 8601 dates
  , model :: Maybe String
  , sessionId :: Maybe String  -- Search within specific session
  , limit :: Maybe Int
  , offset :: Maybe Int
  }

-- | Search result (simplified)
type SearchResultBridge =
  { id :: String
  , type_ :: String  -- "session" | "message" | "file" | "proof" | "recording"
  , title :: String
  , preview :: String
  , score :: Number
  , timestamp :: String  -- ISO 8601
  , metadata :: Json  -- Type-specific metadata
  }

-- | Search response
type SearchResponse =
  { results :: Array SearchResultBridge
  , totalCount :: Int
  , searchTimeMs :: Number
  }

-- | Perform search
performSearch :: WSClient -> SearchRequest -> Aff (Either JsonRpcError SearchResponse)
performSearch client req =
  request client "search.perform" (encodeJson req) decodeResponse
  where
    decodeResponse :: Json -> Aff SearchResponse
    decodeResponse json = case decodeJson json of
      Left err -> throwError (error (show err))
      Right result -> pure result
