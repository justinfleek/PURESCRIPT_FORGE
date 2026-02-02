-- | Shared API types for WebSocket communication
-- | Based on spec 31-WEBSOCKET-PROTOCOL.md
module Sidepanel.Api.Types where

import Prelude
import Data.DateTime (DateTime)
import Argonaut.Core (Json)
import Sidepanel.FFI.DateTime (fromTimestamp, fromISOString, toISOString)
import Data.Number (fromString as Number.fromString)
import Argonaut.Decode.Error (JsonDecodeError(..), TypeMismatch(..))

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
  , data :: Maybe (Record String)
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
import Argonaut.Encode (class EncodeJson, encodeJson, (:=), (:=?))
import Argonaut.Decode (class DecodeJson, decodeJson, (.:), (.:?))
import Argonaut.Core as AC
import Data.DateTime.Instant (unInstant, fromDateTime)
import Data.Time.Duration (Milliseconds(..))

-- | EncodeJson instance for DateTime (as ISO 8601 string)
instance EncodeJson DateTime where
  encodeJson dt = AC.fromString $ toISOString dt

-- | DecodeJson instance for DateTime (from ISO 8601 string or timestamp)
instance DecodeJson DateTime where
  decodeJson json = 
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

-- | EncodeJson instance for BalanceUpdatePayload
instance EncodeJson BalanceUpdatePayload where
  encodeJson payload = AC.fromObject $ AC.fromFoldable
    [ "diem" :=? payload.diem
    , "flk" :=? payload.flk
    , "usd" :=? payload.usd
    , "effective" := payload.effective
    , "consumptionRate" := payload.consumptionRate
    , "timeToDepletion" :=? payload.timeToDepletion
    , "todayUsed" := payload.todayUsed
    , "timestamp" := payload.timestamp
    ]

-- | DecodeJson instance for BalanceUpdatePayload
instance DecodeJson BalanceUpdatePayload where
  decodeJson json = do
    obj <- decodeJson json
    diem <- obj .:? "diem"  -- Optional
    flk <- obj .:? "flk"    -- Optional
    usd <- obj .:? "usd"    -- Optional
    effective <- obj .: "effective"
    consumptionRate <- obj .: "consumptionRate"
    timeToDepletion <- obj .:? "timeToDepletion"
    todayUsed <- obj .: "todayUsed"
    timestamp <- obj .: "timestamp"
    pure { diem, flk, usd, effective, consumptionRate, timeToDepletion, todayUsed, timestamp }

-- | EncodeJson instance for SessionUpdatePayload
instance EncodeJson SessionUpdatePayload where
  encodeJson payload = AC.fromObject $ AC.fromFoldable
    [ "id" := payload.id
    , "model" := payload.model
    , "promptTokens" := payload.promptTokens
    , "completionTokens" := payload.completionTokens
    , "totalTokens" := payload.totalTokens
    , "cost" := payload.cost
    , "messageCount" := payload.messageCount
    ]

-- | DecodeJson instance for SessionUpdatePayload
instance DecodeJson SessionUpdatePayload where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    model <- obj .: "model"
    promptTokens <- obj .: "promptTokens"
    completionTokens <- obj .: "completionTokens"
    totalTokens <- obj .: "totalTokens"
    cost <- obj .: "cost"
    messageCount <- obj .: "messageCount"
    pure { id, model, promptTokens, completionTokens, totalTokens, cost, messageCount }

-- | EncodeJson instance for PositionPayload
instance EncodeJson PositionPayload where
  encodeJson payload = AC.fromObject $ AC.fromFoldable
    [ "line" := payload.line
    , "character" := payload.character
    ]

-- | DecodeJson instance for PositionPayload
instance DecodeJson PositionPayload where
  decodeJson json = do
    obj <- decodeJson json
    line <- obj .: "line"
    character <- obj .: "character"
    pure { line, character }

-- | EncodeJson instance for RangePayload
instance EncodeJson RangePayload where
  encodeJson payload = AC.fromObject $ AC.fromFoldable
    [ "start" := payload.start
    , "end" := payload.end
    ]

-- | DecodeJson instance for RangePayload
instance DecodeJson RangePayload where
  decodeJson json = do
    obj <- decodeJson json
    start <- obj .: "start"
    end <- obj .: "end"
    pure { start, end }

-- | EncodeJson instance for GoalPayload
instance EncodeJson GoalPayload where
  encodeJson payload = AC.fromObject $ AC.fromFoldable
    [ "id" := payload.id
    , "type" := payload.type_
    , "context" := payload.context
    ]

-- | DecodeJson instance for GoalPayload
instance DecodeJson GoalPayload where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    type_ <- obj .: "type"
    context <- obj .: "context"
    pure { id, type_, context }

-- | EncodeJson instance for DiagnosticPayload
instance EncodeJson DiagnosticPayload where
  encodeJson payload = AC.fromObject $ AC.fromFoldable
    [ "severity" := payload.severity
    , "message" := payload.message
    , "range" := payload.range
    ]

-- | DecodeJson instance for DiagnosticPayload
instance DecodeJson DiagnosticPayload where
  decodeJson json = do
    obj <- decodeJson json
    severity <- obj .: "severity"
    message <- obj .: "message"
    range <- obj .: "range"
    pure { severity, message, range }

-- | EncodeJson instance for TacticPayload
instance EncodeJson TacticPayload where
  encodeJson payload = AC.fromObject $ AC.fromFoldable
    [ "name" := payload.name
    , "description" := payload.description
    , "confidence" := payload.confidence
    ]

-- | DecodeJson instance for TacticPayload
instance DecodeJson TacticPayload where
  decodeJson json = do
    obj <- decodeJson json
    name <- obj .: "name"
    description <- obj .: "description"
    confidence <- obj .: "confidence"
    pure { name, description, confidence }

-- | EncodeJson instance for ProofUpdatePayload
instance EncodeJson ProofUpdatePayload where
  encodeJson payload = AC.fromObject $ AC.fromFoldable
    [ "goals" := payload.goals
    , "diagnostics" := payload.diagnostics
    , "tactics" := payload.tactics
    ]

-- | DecodeJson instance for ProofUpdatePayload
instance DecodeJson ProofUpdatePayload where
  decodeJson json = do
    obj <- decodeJson json
    goals <- obj .: "goals"
    diagnostics <- obj .: "diagnostics"
    tactics <- obj .: "tactics"
    pure { goals, diagnostics, tactics }

-- | EncodeJson instance for SnapshotPayload
instance EncodeJson SnapshotPayload where
  encodeJson payload = AC.fromObject $ AC.fromFoldable
    [ "id" := payload.id
    , "timestamp" := payload.timestamp
    , "description" := payload.description
    , "stateHash" := payload.stateHash
    ]

-- | DecodeJson instance for SnapshotPayload
instance DecodeJson SnapshotPayload where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    timestamp <- obj .: "timestamp"
    description <- obj .: "description"
    stateHash <- obj .: "stateHash"
    pure { id, timestamp, description, stateHash }

-- | EncodeJson instance for ConnectionStatusPayload
instance EncodeJson ConnectionStatusPayload where
  encodeJson payload = AC.fromObject $ AC.fromFoldable
    [ "connected" := payload.connected
    , "timestamp" := payload.timestamp
    ]

-- | DecodeJson instance for ConnectionStatusPayload
instance DecodeJson ConnectionStatusPayload where
  decodeJson json = do
    obj <- decodeJson json
    connected <- obj .: "connected"
    timestamp <- obj .: "timestamp"
    pure { connected, timestamp }

-- | EncodeJson instance for NotificationAction
instance EncodeJson NotificationAction where
  encodeJson payload = AC.fromObject $ AC.fromFoldable
    [ "label" := payload.label
    , "actionId" := payload.actionId
    , "primary" := payload.primary
    ]

-- | DecodeJson instance for NotificationAction
instance DecodeJson NotificationAction where
  decodeJson json = do
    obj <- decodeJson json
    label <- obj .: "label"
    actionId <- obj .: "actionId"
    primary <- obj .: "primary"
    pure { label, actionId, primary }

-- | EncodeJson instance for NotificationPayload
instance EncodeJson NotificationPayload where
  encodeJson payload = AC.fromObject $ AC.fromFoldable
    [ "id" := payload.id
    , "type" := payload.type_
    , "level" := payload.level
    , "title" := payload.title
    , "message" :=? payload.message
    , "createdAt" := payload.createdAt
    , "duration" :=? payload.duration
    , "actions" := payload.actions
    , "dismissible" := payload.dismissible
    , "persistent" := payload.persistent
    ]

-- | DecodeJson instance for NotificationPayload
instance DecodeJson NotificationPayload where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    type_ <- obj .: "type"
    level <- obj .: "level"
    title <- obj .: "title"
    message <- obj .:? "message"
    createdAt <- obj .: "createdAt"
    duration <- obj .:? "duration"
    actions <- obj .: "actions"
    dismissible <- obj .: "dismissible"
    persistent <- obj .: "persistent"
    pure { id, type_, level, title, message, createdAt, duration, actions, dismissible, persistent }

-- | EncodeJson instance for JsonRpcError
instance EncodeJson JsonRpcError where
  encodeJson err = AC.fromObject $ AC.fromFoldable
    [ "code" := err.code
    , "message" := err.message
    , "data" :=? err.data
    ]

-- | DecodeJson instance for JsonRpcError
instance DecodeJson JsonRpcError where
  decodeJson json = do
    obj <- decodeJson json
    code <- obj .: "code"
    message <- obj .: "message"
    data <- obj .:? "data"
    pure { code, message, data }

-- | EncodeJson instance for ServerMessage
instance EncodeJson ServerMessage where
  encodeJson = case _ of
    BalanceUpdate payload -> AC.fromObject $ AC.fromFoldable
      [ "type" := AC.fromString "balance.update"
      , "payload" := encodeJson payload
      ]
    SessionUpdate payload -> AC.fromObject $ AC.fromFoldable
      [ "type" := AC.fromString "session.update"
      , "payload" := encodeJson payload
      ]
    ProofUpdate payload -> AC.fromObject $ AC.fromFoldable
      [ "type" := AC.fromString "proof.update"
      , "payload" := encodeJson payload
      ]
    SnapshotCreated payload -> AC.fromObject $ AC.fromFoldable
      [ "type" := AC.fromString "snapshot.created"
      , "payload" := encodeJson payload
      ]
    ConnectionStatus payload -> AC.fromObject $ AC.fromFoldable
      [ "type" := AC.fromString "connection.status"
      , "payload" := encodeJson payload
      ]
    Notification payload -> AC.fromObject $ AC.fromFoldable
      [ "type" := AC.fromString "notification"
      , "payload" := encodeJson payload
      ]
    Error err -> AC.fromObject $ AC.fromFoldable
      [ "type" := AC.fromString "error"
      , "error" := encodeJson err
      ]

-- | DecodeJson instance for ServerMessage
instance DecodeJson ServerMessage where
  decodeJson json = do
    obj <- decodeJson json
    type_ <- obj .: "type"
    case type_ of
      "balance.update" -> do
        payload <- obj .: "payload"
        pure $ BalanceUpdate payload
      "session.update" -> do
        payload <- obj .: "payload"
        pure $ SessionUpdate payload
      "proof.update" -> do
        payload <- obj .: "payload"
        pure $ ProofUpdate payload
      "snapshot.created" -> do
        payload <- obj .: "payload"
        pure $ SnapshotCreated payload
      "connection.status" -> do
        payload <- obj .: "payload"
        pure $ ConnectionStatus payload
      "notification" -> do
        payload <- obj .: "payload"
        pure $ Notification payload
      "error" -> do
        err <- obj .: "error"
        pure $ Error err
      _ -> Left $ TypeMismatch "ServerMessage"
