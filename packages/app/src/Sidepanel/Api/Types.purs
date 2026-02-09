-- | Shared API types for WebSocket communication
-- | Based on spec 31-WEBSOCKET-PROTOCOL.md
module Sidepanel.Api.Types where

import Prelude
import Data.DateTime (DateTime)
import Data.Maybe (Maybe(..))
import Data.Argonaut.Core (Json)
import Data.Array as Array
import Data.Argonaut.Encode (class EncodeJson, encodeJson, (:=), (:=?))
import Data.Argonaut.Decode (class DecodeJson, decodeJson, (.:), (.:?))
import Data.Argonaut.Core as AC
import Data.Argonaut.Decode.Error (JsonDecodeError(TypeMismatch))
import Data.DateTime.Instant (unInstant, fromDateTime)
import Data.Either (Either(..))
import Data.Time.Duration (Milliseconds(..))
import Data.Number as Number
import Data.Traversable (traverse)
import Data.Tuple (Tuple)
import Foreign.Object as FO
import Sidepanel.FFI.DateTime (fromTimestamp, fromISOString, toISOString)

-- | JSON-RPC 2.0 Request
type JsonRpcRequest =
  { jsonrpc :: String  -- "2.0"
  , id :: Maybe String
  , method :: String
  , params :: JsonRpcParams
  }

-- | JSON-RPC 2.0 Response
type JsonRpcResponse =
  { jsonrpc :: String  -- "2.0"
  , id :: Maybe String
  , result :: Maybe JsonRpcResult
  , error :: Maybe JsonRpcError
  }

-- | JSON-RPC Parameters (JSON value)
type JsonRpcParams = Json

-- | JSON-RPC Result (JSON value)
type JsonRpcResult = Json

-- | JSON-RPC Error
type JsonRpcError =
  { code :: Int
  , message :: String
  , errorData :: Maybe String
  }

-- | Server message types
data ServerMessage
  = BalanceUpdate BalanceUpdatePayload
  | SessionUpdate SessionUpdatePayload
  | ProofUpdate ProofUpdatePayload
  | SnapshotCreated SnapshotPayload
  | ConnectionStatus ConnectionStatusPayload
  | Notification NotificationPayload
  | Error JsonRpcError

-- | Balance update payload
-- | Note: Either Venice fields (diem/usd) or FLK field should be provided, not both
type BalanceUpdatePayload =
  { diem :: Maybe Number      -- Venice Diem (optional)
  , flk :: Maybe Number        -- Fleek Token balance (optional)
  , usd :: Maybe Number       -- Venice USD (optional)
  , effective :: Number
  , consumptionRate :: Number
  , timeToDepletion :: Maybe Number
  , todayUsed :: Number
  , timestamp :: DateTime
  }

-- | Session update payload
type SessionUpdatePayload =
  { id :: String
  , model :: String
  , promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  , cost :: Number
  , messageCount :: Int
  }

-- | Proof update payload
type ProofUpdatePayload =
  { goals :: Array GoalPayload
  , diagnostics :: Array DiagnosticPayload
  , tactics :: Array TacticPayload
  }

type GoalPayload =
  { id :: String
  , type_ :: String
  , context :: String
  }

type DiagnosticPayload =
  { severity :: String
  , message :: String
  , range :: RangePayload
  }

type RangePayload =
  { start :: PositionPayload
  , end :: PositionPayload
  }

type PositionPayload =
  { line :: Int
  , character :: Int
  }

type TacticPayload =
  { name :: String
  , description :: String
  , confidence :: Number
  }

-- | Snapshot payload
type SnapshotPayload =
  { id :: String
  , timestamp :: DateTime
  , description :: String
  , stateHash :: String
  }

-- | Connection status payload
type ConnectionStatusPayload =
  { connected :: Boolean
  , timestamp :: DateTime
  }

-- | Notification payload (Spec 36)
type NotificationPayload =
  { id :: String
  , type_ :: String  -- "toast" | "banner" | "inline" | "silent"
  , level :: String  -- "success" | "info" | "warning" | "error"
  , title :: String
  , message :: Maybe String
  , createdAt :: String  -- ISO timestamp
  , duration :: Maybe Number  -- milliseconds
  , actions :: Array NotificationAction
  , dismissible :: Boolean
  , persistent :: Boolean
  }

type NotificationAction =
  { label :: String
  , actionId :: String
  , primary :: Boolean
  }

-- | Client message types
data ClientMessage
  = RequestSnapshot String
  | RestoreSnapshot String
  | RequestBalance
  | RequestSession String
  | RequestProof String

-- | Argonaut codecs for ServerMessage and payload types

-- | Encode DateTime as ISO 8601 string (standalone function, not orphan instance)
encodeDateTime :: DateTime -> Json
encodeDateTime dt = AC.fromString $ toISOString dt

-- | Decode DateTime from ISO 8601 string or timestamp (standalone function, not orphan instance)
decodeDateTime :: Json -> Either JsonDecodeError DateTime
decodeDateTime json =
    -- Try parsing as number (milliseconds since epoch) first
    case decodeJson json :: Either JsonDecodeError Number of
      Right num -> Right $ fromTimestamp num
      Left _ ->
        -- Try parsing as ISO 8601 string
        case decodeJson json :: Either JsonDecodeError String of
          Right str ->
            -- Try parsing as numeric string first (for backward compatibility)
            case Number.fromString str of
              Just num -> Right $ fromTimestamp num
              Nothing ->
                -- Parse as ISO 8601 string using FFI
                Right $ fromISOString str
          Left err -> Left err

-- | Standalone encoder for BalanceUpdatePayload (type alias cannot have typeclass instances)
encodeBalanceUpdatePayload :: BalanceUpdatePayload -> Json
encodeBalanceUpdatePayload payload = AC.fromObject $ FO.fromFoldable $ Array.catMaybes
    [ "diem" :=? payload.diem
    , "flk" :=? payload.flk
    , "usd" :=? payload.usd
    , Just ("effective" := payload.effective)
    , Just ("consumptionRate" := payload.consumptionRate)
    , "timeToDepletion" :=? payload.timeToDepletion
    , Just ("todayUsed" := payload.todayUsed)
    , Just ("timestamp" := encodeDateTime payload.timestamp)
    ]

-- | Standalone decoder for BalanceUpdatePayload (type alias cannot have typeclass instances)
decodeBalanceUpdatePayload :: Json -> Either JsonDecodeError BalanceUpdatePayload
decodeBalanceUpdatePayload json = do
    obj <- decodeJson json
    diem <- obj .:? "diem"
    flk <- obj .:? "flk"
    usd <- obj .:? "usd"
    effective <- obj .: "effective"
    consumptionRate <- obj .: "consumptionRate"
    timeToDepletion <- obj .:? "timeToDepletion"
    todayUsed <- obj .: "todayUsed"
    timestampJson <- obj .: "timestamp"
    timestamp <- decodeDateTime timestampJson
    pure { diem, flk, usd, effective, consumptionRate, timeToDepletion, todayUsed, timestamp }

-- | Standalone encoder for SessionUpdatePayload
encodeSessionUpdatePayload :: SessionUpdatePayload -> Json
encodeSessionUpdatePayload payload = AC.fromObject $ FO.fromFoldable
    [ "id" := payload.id
    , "model" := payload.model
    , "promptTokens" := payload.promptTokens
    , "completionTokens" := payload.completionTokens
    , "totalTokens" := payload.totalTokens
    , "cost" := payload.cost
    , "messageCount" := payload.messageCount
    ]

-- | Standalone decoder for SessionUpdatePayload
decodeSessionUpdatePayload :: Json -> Either JsonDecodeError SessionUpdatePayload
decodeSessionUpdatePayload json = do
    obj <- decodeJson json
    id <- obj .: "id"
    model <- obj .: "model"
    promptTokens <- obj .: "promptTokens"
    completionTokens <- obj .: "completionTokens"
    totalTokens <- obj .: "totalTokens"
    cost <- obj .: "cost"
    messageCount <- obj .: "messageCount"
    pure { id, model, promptTokens, completionTokens, totalTokens, cost, messageCount }

-- | Standalone encoder for PositionPayload
encodePositionPayload :: PositionPayload -> Json
encodePositionPayload payload = AC.fromObject $ FO.fromFoldable
    [ "line" := payload.line
    , "character" := payload.character
    ]

-- | Standalone decoder for PositionPayload
decodePositionPayload :: Json -> Either JsonDecodeError PositionPayload
decodePositionPayload json = do
    obj <- decodeJson json
    line <- obj .: "line"
    character <- obj .: "character"
    pure { line, character }

-- | Standalone encoder for RangePayload
encodeRangePayload :: RangePayload -> Json
encodeRangePayload payload = AC.fromObject $ FO.fromFoldable
    [ "start" := encodePositionPayload payload.start
    , "end" := encodePositionPayload payload.end
    ]

-- | Standalone decoder for RangePayload
decodeRangePayload :: Json -> Either JsonDecodeError RangePayload
decodeRangePayload json = do
    obj <- decodeJson json
    startJson <- obj .: "start"
    start <- decodePositionPayload startJson
    endJson <- obj .: "end"
    end <- decodePositionPayload endJson
    pure { start, end }

-- | Standalone encoder for GoalPayload
encodeGoalPayload :: GoalPayload -> Json
encodeGoalPayload payload = AC.fromObject $ FO.fromFoldable
    [ "id" := payload.id
    , "type" := payload.type_
    , "context" := payload.context
    ]

-- | Standalone decoder for GoalPayload
decodeGoalPayload :: Json -> Either JsonDecodeError GoalPayload
decodeGoalPayload json = do
    obj <- decodeJson json
    id <- obj .: "id"
    type_ <- obj .: "type"
    context <- obj .: "context"
    pure { id, type_, context }

-- | Standalone encoder for DiagnosticPayload
encodeDiagnosticPayload :: DiagnosticPayload -> Json
encodeDiagnosticPayload payload = AC.fromObject $ FO.fromFoldable
    [ "severity" := payload.severity
    , "message" := payload.message
    , "range" := encodeRangePayload payload.range
    ]

-- | Standalone decoder for DiagnosticPayload
decodeDiagnosticPayload :: Json -> Either JsonDecodeError DiagnosticPayload
decodeDiagnosticPayload json = do
    obj <- decodeJson json
    severity <- obj .: "severity"
    message <- obj .: "message"
    rangeJson <- obj .: "range"
    range <- decodeRangePayload rangeJson
    pure { severity, message, range }

-- | Standalone encoder for TacticPayload
encodeTacticPayload :: TacticPayload -> Json
encodeTacticPayload payload = AC.fromObject $ FO.fromFoldable
    [ "name" := payload.name
    , "description" := payload.description
    , "confidence" := payload.confidence
    ]

-- | Standalone decoder for TacticPayload
decodeTacticPayload :: Json -> Either JsonDecodeError TacticPayload
decodeTacticPayload json = do
    obj <- decodeJson json
    name <- obj .: "name"
    description <- obj .: "description"
    confidence <- obj .: "confidence"
    pure { name, description, confidence }

-- | Standalone encoder for ProofUpdatePayload
encodeProofUpdatePayload :: ProofUpdatePayload -> Json
encodeProofUpdatePayload payload = AC.fromObject $ FO.fromFoldable
    [ "goals" := map encodeGoalPayload payload.goals
    , "diagnostics" := map encodeDiagnosticPayload payload.diagnostics
    , "tactics" := map encodeTacticPayload payload.tactics
    ]

-- | Standalone decoder for ProofUpdatePayload
decodeProofUpdatePayload :: Json -> Either JsonDecodeError ProofUpdatePayload
decodeProofUpdatePayload json = do
    obj <- decodeJson json
    goalsJson <- obj .: "goals"
    goals <- traverse decodeGoalPayload goalsJson
    diagnosticsJson <- obj .: "diagnostics"
    diagnostics <- traverse decodeDiagnosticPayload diagnosticsJson
    tacticsJson <- obj .: "tactics"
    tactics <- traverse decodeTacticPayload tacticsJson
    pure { goals, diagnostics, tactics }

-- | Standalone encoder for SnapshotPayload
encodeSnapshotPayload :: SnapshotPayload -> Json
encodeSnapshotPayload payload = AC.fromObject $ FO.fromFoldable
    [ "id" := payload.id
    , "timestamp" := encodeDateTime payload.timestamp
    , "description" := payload.description
    , "stateHash" := payload.stateHash
    ]

-- | Standalone decoder for SnapshotPayload
decodeSnapshotPayload :: Json -> Either JsonDecodeError SnapshotPayload
decodeSnapshotPayload json = do
    obj <- decodeJson json
    id <- obj .: "id"
    timestampJson <- obj .: "timestamp"
    timestamp <- decodeDateTime timestampJson
    description <- obj .: "description"
    stateHash <- obj .: "stateHash"
    pure { id, timestamp, description, stateHash }

-- | Standalone encoder for ConnectionStatusPayload
encodeConnectionStatusPayload :: ConnectionStatusPayload -> Json
encodeConnectionStatusPayload payload = AC.fromObject $ FO.fromFoldable
    [ "connected" := payload.connected
    , "timestamp" := encodeDateTime payload.timestamp
    ]

-- | Standalone decoder for ConnectionStatusPayload
decodeConnectionStatusPayload :: Json -> Either JsonDecodeError ConnectionStatusPayload
decodeConnectionStatusPayload json = do
    obj <- decodeJson json
    connected <- obj .: "connected"
    timestampJson <- obj .: "timestamp"
    timestamp <- decodeDateTime timestampJson
    pure { connected, timestamp }

-- | Standalone encoder for NotificationAction
encodeNotificationAction :: NotificationAction -> Json
encodeNotificationAction payload = AC.fromObject $ FO.fromFoldable
    [ "label" := payload.label
    , "actionId" := payload.actionId
    , "primary" := payload.primary
    ]

-- | Standalone decoder for NotificationAction
decodeNotificationAction :: Json -> Either JsonDecodeError NotificationAction
decodeNotificationAction json = do
    obj <- decodeJson json
    label <- obj .: "label"
    actionId <- obj .: "actionId"
    primary <- obj .: "primary"
    pure { label, actionId, primary }

-- | Standalone encoder for NotificationPayload
encodeNotificationPayload :: NotificationPayload -> Json
encodeNotificationPayload payload = AC.fromObject $ FO.fromFoldable $ Array.catMaybes
    [ Just ("id" := payload.id)
    , Just ("type" := payload.type_)
    , Just ("level" := payload.level)
    , Just ("title" := payload.title)
    , "message" :=? payload.message
    , Just ("createdAt" := payload.createdAt)
    , "duration" :=? payload.duration
    , Just ("actions" := map encodeNotificationAction payload.actions)
    , Just ("dismissible" := payload.dismissible)
    , Just ("persistent" := payload.persistent)
    ]

-- | Standalone decoder for NotificationPayload
decodeNotificationPayload :: Json -> Either JsonDecodeError NotificationPayload
decodeNotificationPayload json = do
    obj <- decodeJson json
    id <- obj .: "id"
    type_ <- obj .: "type"
    level <- obj .: "level"
    title <- obj .: "title"
    message <- obj .:? "message"
    createdAt <- obj .: "createdAt"
    duration <- obj .:? "duration"
    actionsJson <- obj .: "actions"
    actions <- traverse decodeNotificationAction actionsJson
    dismissible <- obj .: "dismissible"
    persistent <- obj .: "persistent"
    pure { id, type_, level, title, message, createdAt, duration, actions, dismissible, persistent }

-- | Standalone encoder for JsonRpcError
encodeJsonRpcError :: JsonRpcError -> Json
encodeJsonRpcError err = AC.fromObject $ FO.fromFoldable $ Array.catMaybes
    [ Just ("code" := err.code)
    , Just ("message" := err.message)
    , "data" :=? err.errorData
    ]

-- | Standalone decoder for JsonRpcError
decodeJsonRpcError :: Json -> Either JsonDecodeError JsonRpcError
decodeJsonRpcError json = do
    obj <- decodeJson json
    code <- obj .: "code"
    message <- obj .: "message"
    data_ <- obj .:? "data"
    pure { code: code, message: message, errorData: data_ }

-- | EncodeJson instance for ServerMessage (data type, valid for typeclass instances)
instance EncodeJson ServerMessage where
  encodeJson = case _ of
    BalanceUpdate payload -> AC.fromObject $ FO.fromFoldable
      [ "type" := AC.fromString "balance.update"
      , "payload" := encodeBalanceUpdatePayload payload
      ]
    SessionUpdate payload -> AC.fromObject $ FO.fromFoldable
      [ "type" := AC.fromString "session.update"
      , "payload" := encodeSessionUpdatePayload payload
      ]
    ProofUpdate payload -> AC.fromObject $ FO.fromFoldable
      [ "type" := AC.fromString "proof.update"
      , "payload" := encodeProofUpdatePayload payload
      ]
    SnapshotCreated payload -> AC.fromObject $ FO.fromFoldable
      [ "type" := AC.fromString "snapshot.created"
      , "payload" := encodeSnapshotPayload payload
      ]
    ConnectionStatus payload -> AC.fromObject $ FO.fromFoldable
      [ "type" := AC.fromString "connection.status"
      , "payload" := encodeConnectionStatusPayload payload
      ]
    Notification payload -> AC.fromObject $ FO.fromFoldable
      [ "type" := AC.fromString "notification"
      , "payload" := encodeNotificationPayload payload
      ]
    Error err -> AC.fromObject $ FO.fromFoldable
      [ "type" := AC.fromString "error"
      , "error" := encodeJsonRpcError err
      ]

-- | DecodeJson instance for ServerMessage (data type, valid for typeclass instances)
instance DecodeJson ServerMessage where
  decodeJson json = do
    obj <- decodeJson json
    type_ <- obj .: "type"
    case type_ of
      "balance.update" -> do
        payloadJson <- obj .: "payload"
        payload <- decodeBalanceUpdatePayload payloadJson
        pure $ BalanceUpdate payload
      "session.update" -> do
        payloadJson <- obj .: "payload"
        payload <- decodeSessionUpdatePayload payloadJson
        pure $ SessionUpdate payload
      "proof.update" -> do
        payloadJson <- obj .: "payload"
        payload <- decodeProofUpdatePayload payloadJson
        pure $ ProofUpdate payload
      "snapshot.created" -> do
        payloadJson <- obj .: "payload"
        payload <- decodeSnapshotPayload payloadJson
        pure $ SnapshotCreated payload
      "connection.status" -> do
        payloadJson <- obj .: "payload"
        payload <- decodeConnectionStatusPayload payloadJson
        pure $ ConnectionStatus payload
      "notification" -> do
        payloadJson <- obj .: "payload"
        payload <- decodeNotificationPayload payloadJson
        pure $ Notification payload
      "error" -> do
        errJson <- obj .: "error"
        err <- decodeJsonRpcError errJson
        pure $ Error err
      _ -> Left $ TypeMismatch "ServerMessage"
