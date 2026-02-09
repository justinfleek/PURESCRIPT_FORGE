-- | Bridge Server API Helpers
-- | Convenience functions for calling bridge server JSON-RPC methods
module Sidepanel.Api.Bridge where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.DateTime (DateTime)
import Sidepanel.WebSocket.Client (WSClient, request)
import Sidepanel.Api.Types (JsonRpcError)
import Argonaut.Core as AC
import Argonaut.Core (Json)
import Argonaut.Decode (class DecodeJson, decodeJson, (.:), (.:?))
import Argonaut.Encode (class EncodeJson, encodeJson, (:=), (:=?))
import Argonaut.Parser (jsonParser)
import Data.Either (Either, either)
import Data.Argonaut.Decode.Error (JsonDecodeError)

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

-- | File context add response JSON codec
instance EncodeJson FileContextAddRequest where
  encodeJson req = encodeJson
    { path: req.path
    , sessionId: req.sessionId
    }

instance DecodeJson FileContextAddResponse where
  decodeJson json = do
    obj <- decodeJson json
    success <- obj .: "success"
    tokens <- obj .: "tokens"
    contextBudget <- obj .: "contextBudget"
    used <- contextBudget .: "used"
    total <- contextBudget .: "total"
    pure { success, tokens, contextBudget: { used, total } }

-- | Add file to context
addFileToContext :: WSClient -> FileContextAddRequest -> Aff (Either JsonRpcError FileContextAddResponse)
addFileToContext client req = do
  result <- request client "file.context.add" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError FileContextAddResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right result -> pure $ Right result
    printJsonDecodeError :: JsonDecodeError -> String
    printJsonDecodeError err = show err

-- | File context list response JSON codec
instance EncodeJson FileContextListRequest where
  encodeJson req = encodeJson
    { sessionId: req.sessionId
    , filter: req.filter
    }

instance DecodeJson FileInContext where
  decodeJson json = do
    obj <- decodeJson json
    path <- obj .: "path"
    tokens <- obj .: "tokens"
    readAt <- obj .: "readAt"
    status <- obj .: "status"
    language <- obj .: "language"
    size <- obj .: "size"
    pure { path, tokens, readAt, status, language, size }

instance DecodeJson FileContextListResponse where
  decodeJson json = do
    obj <- decodeJson json
    files <- obj .: "files"
    contextBudget <- obj .: "contextBudget"
    used <- contextBudget .: "used"
    total <- contextBudget .: "total"
    pure { files, contextBudget: { used, total } }

-- | List files in context
listFilesInContext :: WSClient -> FileContextListRequest -> Aff (Either JsonRpcError FileContextListResponse)
listFilesInContext client req = do
  result <- request client "file.context.list" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError FileContextListResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right result -> pure $ Right result
    printJsonDecodeError :: JsonDecodeError -> String
    printJsonDecodeError err = show err

-- | Terminal execute response JSON codec
instance EncodeJson TerminalExecuteRequest where
  encodeJson req = encodeJson
    { command: req.command
    , cwd: req.cwd
    , sessionId: req.sessionId
    }

instance DecodeJson TerminalExecuteResponse where
  decodeJson json = do
    obj <- decodeJson json
    success <- obj .: "success"
    output <- obj .:? "output"
    exitCode <- obj .:? "exitCode"
    pure { success, output, exitCode }

-- | Execute terminal command
executeTerminalCommand :: WSClient -> TerminalExecuteRequest -> Aff (Either JsonRpcError TerminalExecuteResponse)
executeTerminalCommand client req = do
  result <- request client "terminal.execute" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError TerminalExecuteResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right result -> pure $ Right result
    printJsonDecodeError :: JsonDecodeError -> String
    printJsonDecodeError err = show err

-- | Session new response JSON codec
instance EncodeJson SessionNewRequest where
  encodeJson req = encodeJson
    { name: req.name
    , parentId: req.parentId
    , model: req.model
    , provider: req.provider
    }

instance DecodeJson SessionNewResponse where
  decodeJson json = do
    obj <- decodeJson json
    sessionId <- obj .: "sessionId"
    success <- obj .: "success"
    pure { sessionId, success }

-- | Create new session
createNewSession :: WSClient -> SessionNewRequest -> Aff (Either JsonRpcError SessionNewResponse)
createNewSession client req = do
  result <- request client "session.new" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError SessionNewResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right result -> pure $ Right result
    printJsonDecodeError :: JsonDecodeError -> String
    printJsonDecodeError err = show err

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

-- | File read request JSON codec
instance EncodeJson FileReadRequest where
  encodeJson req = encodeJson
    { path: req.path
    }

instance DecodeJson FileReadResponse where
  decodeJson json = do
    obj <- decodeJson json
    success <- obj .: "success"
    content <- obj .:? "content"
    error <- obj .:? "error"
    pure { success, content, error }

-- | Read file content
readFileContent :: WSClient -> FileReadRequest -> Aff (Either JsonRpcError FileReadResponse)
readFileContent client req = do
  result <- request client "file.read" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError FileReadResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right result -> pure $ Right result
    printJsonDecodeError :: JsonDecodeError -> String
    printJsonDecodeError err = show err

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

instance EncodeJson SnapshotListRequest where
  encodeJson req = encodeJson
    { limit: req.limit
    , offset: req.offset
    }

instance DecodeJson SnapshotSummary where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    timestamp <- obj .: "timestamp"
    description <- obj .:? "description"
    pure { id, timestamp, description }

instance DecodeJson SnapshotListResponse where
  decodeJson json = do
    obj <- decodeJson json
    snapshots <- obj .: "snapshots"
    pure { snapshots }

instance EncodeJson SnapshotSaveRequest where
  encodeJson req = encodeJson
    { trigger: req.trigger
    , description: req.description
    }

instance DecodeJson SnapshotSaveResponse where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    success <- obj .: "success"
    pure { id, success }

instance EncodeJson SnapshotRestoreRequest where
  encodeJson req = encodeJson { id: req.id }

instance DecodeJson SnapshotRestoreResponse where
  decodeJson json = do
    obj <- decodeJson json
    success <- obj .: "success"
    pure { success }

-- | List snapshots
listSnapshots :: WSClient -> SnapshotListRequest -> Aff (Either JsonRpcError SnapshotListResponse)
listSnapshots client req = do
  result <- request client "snapshot.list" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError SnapshotListResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right result -> pure $ Right result
    printJsonDecodeError :: JsonDecodeError -> String
    printJsonDecodeError err = show err

-- | Save snapshot
saveSnapshot :: WSClient -> SnapshotSaveRequest -> Aff (Either JsonRpcError SnapshotSaveResponse)
saveSnapshot client req = do
  result <- request client "snapshot.save" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError SnapshotSaveResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right result -> pure $ Right result
    printJsonDecodeError :: JsonDecodeError -> String
    printJsonDecodeError err = show err

-- | Restore snapshot
restoreSnapshot :: WSClient -> SnapshotRestoreRequest -> Aff (Either JsonRpcError SnapshotRestoreResponse)
restoreSnapshot client req = do
  result <- request client "snapshot.restore" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError SnapshotRestoreResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right result -> pure $ Right result
    printJsonDecodeError :: JsonDecodeError -> String
    printJsonDecodeError err = show err

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
  , session :: Maybe SessionState
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
  { venice :: { diem :: Number, usd :: Number, effective :: Number, lastUpdated :: Maybe DateTime }
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

instance EncodeJson SnapshotGetRequest where
  encodeJson req = encodeJson { id: req.id }

instance DecodeJson FileContextEntry where
  decodeJson json = do
    obj <- decodeJson json
    path <- obj .: "path"
    tokens <- obj .: "tokens"
    language <- obj .: "language"
    pure { path, tokens, language }

instance DecodeJson SnapshotGetState where
  decodeJson json = do
    obj <- decodeJson json
    balance <- obj .:? "balance"
    session <- obj .:? "session"
    proof <- obj .:? "proof"
    metrics <- obj .:? "metrics"
    fileContext <- obj .:? "fileContext"
    pure
      { balance
      , session
      , proof
      , metrics
      , fileContext: fromMaybe [] fileContext
      }

instance DecodeJson SnapshotGetResponse where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    timestamp <- obj .: "timestamp"
    description <- obj .:? "description"
    state <- obj .: "state"
    pure { id, timestamp, description, state }

-- | Get snapshot by ID
getSnapshot :: WSClient -> SnapshotGetRequest -> Aff (Either JsonRpcError SnapshotGetResponse)
getSnapshot client req = do
  result <- request client "snapshot.get" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError SnapshotGetResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right result -> pure $ Right result
    printJsonDecodeError :: JsonDecodeError -> String
    printJsonDecodeError err = show err

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

instance EncodeJson LeanCheckRequest where
  encodeJson req = encodeJson { file: req.file }

instance DecodeJson LeanDiagnostic where
  decodeJson json = do
    obj <- decodeJson json
    severity <- obj .: "severity"
    message <- obj .: "message"
    range <- obj .: "range"
    start <- range .: "start"
    end <- range .: "end"
    startLine <- start .: "line"
    startCol <- start .: "col"
    endLine <- end .: "line"
    endCol <- end .: "col"
    pure
      { severity
      , message
      , range:
          { start: { line: startLine, col: startCol }
          , end: { line: endLine, col: endCol }
          }
      }

instance DecodeJson LeanCheckResponse where
  decodeJson json = do
    obj <- decodeJson json
    diagnostics <- obj .: "diagnostics"
    pure { diagnostics }

instance EncodeJson LeanGoalsRequest where
  encodeJson req = encodeJson
    { file: req.file
    , line: req.line
    , column: req.column
    }

instance DecodeJson LeanGoal where
  decodeJson json = do
    obj <- decodeJson json
    type_ <- obj .: "type"
    context <- obj .: "context"
    pure { type_, context }

instance DecodeJson LeanGoalsResponse where
  decodeJson json = do
    obj <- decodeJson json
    goals <- obj .: "goals"
    pure { goals }

-- | Check Lean file
checkLeanFile :: WSClient -> LeanCheckRequest -> Aff (Either JsonRpcError LeanCheckResponse)
checkLeanFile client req = do
  result <- request client "lean.check" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError LeanCheckResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right result -> pure $ Right result
    printJsonDecodeError :: JsonDecodeError -> String
    printJsonDecodeError err = show err

-- | Get Lean goals
getLeanGoals :: WSClient -> LeanGoalsRequest -> Aff (Either JsonRpcError LeanGoalsResponse)
getLeanGoals client req = do
  result <- request client "lean.goals" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError LeanGoalsResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right result -> pure $ Right result
    printJsonDecodeError :: JsonDecodeError -> String
    printJsonDecodeError err = show err

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

instance EncodeJson LeanApplyTacticRequest where
  encodeJson req = AC.fromObject $ AC.fromFoldable
    [ "file" := req.file
    , "line" := req.line
    , "column" := req.column
    , "tactic" := req.tactic
    , "goalIndex" :=? req.goalIndex
    ]

instance DecodeJson LeanApplyTacticResponse where
  decodeJson json = do
    obj <- decodeJson json
    success <- obj .: "success"
    message <- obj .:? "message"
    goals <- obj .: "goals"
    pure { success, message, goals }

-- | Apply Lean tactic
applyLeanTactic :: WSClient -> LeanApplyTacticRequest -> Aff (Either JsonRpcError LeanApplyTacticResponse)
applyLeanTactic client req = do
  result <- request client "lean.applyTactic" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError LeanApplyTacticResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right result -> pure $ Right result
    printJsonDecodeError :: JsonDecodeError -> String
    printJsonDecodeError err = show err

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

instance EncodeJson LeanSearchTheoremsRequest where
  encodeJson req = AC.fromObject $ AC.fromFoldable
    [ "query" := req.query
    , "limit" :=? req.limit
    , "file" :=? req.file
    ]

instance DecodeJson TheoremResult where
  decodeJson json = do
    obj <- decodeJson json
    name <- obj .: "name"
    statement <- obj .: "statement"
    file <- obj .: "file"
    line <- obj .: "line"
    description <- obj .:? "description"
    pure { name, statement, file, line, description }

instance DecodeJson LeanSearchTheoremsResponse where
  decodeJson json = do
    obj <- decodeJson json
    theorems <- obj .: "theorems"
    total <- obj .: "total"
    pure { theorems, total }

-- | Search Lean theorems
searchLeanTheorems :: WSClient -> LeanSearchTheoremsRequest -> Aff (Either JsonRpcError LeanSearchTheoremsResponse)
searchLeanTheorems client req = do
  result <- request client "lean.searchTheorems" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError LeanSearchTheoremsResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right result -> pure $ Right result
    printJsonDecodeError :: JsonDecodeError -> String
    printJsonDecodeError err = show err

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

instance EncodeJson SettingsSaveRequest where
  encodeJson req = encodeJson
    { alerts: req.alerts
    , appearance: req.appearance
    , keyboard: req.keyboard
    , features: req.features
    , storage: req.storage
    }

instance DecodeJson SettingsSaveResponse where
  decodeJson json = do
    obj <- decodeJson json
    success <- obj .: "success"
    pure { success }

-- | Save settings to bridge server
saveSettings :: WSClient -> SettingsSaveRequest -> Aff (Either JsonRpcError SettingsSaveResponse)
saveSettings client req = do
  result <- request client "settings.save" (encodeJson req) decodeResponse
  pure result
  where
    decodeResponse :: Json -> Aff (Either JsonRpcError SettingsSaveResponse)
    decodeResponse json = do
      case decodeJson json of
        Left err -> pure $ Left { code: -32700, message: "Parse error: " <> printJsonDecodeError err, data: Nothing }
        Right result -> pure $ Right result
    printJsonDecodeError :: JsonDecodeError -> String
    printJsonDecodeError err = show err
