-- | Bridge API - Session and Snapshot Operations
-- |
-- | Session management and snapshot persistence operations.
-- |
-- | Coeffect Equation:
-- |   SessionOps : WSClient -> Request -> Aff (Either Error Response)
-- |   with state tracking: Session^n -o Snapshot^m
-- |   where snapshots preserve session state across time
-- |
-- | Module Coverage: session.new, snapshot.list, snapshot.save, snapshot.restore, snapshot.get
module Sidepanel.Api.Bridge.Session
  ( -- * Session Operations
    createNewSession
    -- * Snapshot Operations
  , listSnapshots
  , saveSnapshot
  , restoreSnapshot
  , getSnapshot
  ) where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Argonaut.Core (Json)
import Argonaut.Decode (class DecodeJson, decodeJson, (.:), (.:?))
import Argonaut.Encode (class EncodeJson, encodeJson)
import Sidepanel.WebSocket.Client (WSClient, request)
import Sidepanel.Api.Types (JsonRpcError)
import Sidepanel.Api.Bridge.Types
  ( SessionNewRequest
  , SessionNewResponse
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
  , FileContextEntry
  , printJsonDecodeError
  )

--------------------------------------------------------------------------------
-- | JSON Instances - Session
--------------------------------------------------------------------------------

instance encodeSessionNewRequest :: EncodeJson SessionNewRequest where
  encodeJson req = encodeJson
    { name: req.name
    , parentId: req.parentId
    , model: req.model
    , provider: req.provider
    }

instance decodeSessionNewResponse :: DecodeJson SessionNewResponse where
  decodeJson json = do
    obj <- decodeJson json
    sessionId <- obj .: "sessionId"
    success <- obj .: "success"
    pure { sessionId, success }

--------------------------------------------------------------------------------
-- | JSON Instances - Snapshot
--------------------------------------------------------------------------------

instance encodeSnapshotListRequest :: EncodeJson SnapshotListRequest where
  encodeJson req = encodeJson
    { limit: req.limit
    , offset: req.offset
    }

instance decodeSnapshotSummary :: DecodeJson SnapshotSummary where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    timestamp <- obj .: "timestamp"
    description <- obj .:? "description"
    pure { id, timestamp, description }

instance decodeSnapshotListResponse :: DecodeJson SnapshotListResponse where
  decodeJson json = do
    obj <- decodeJson json
    snapshots <- obj .: "snapshots"
    pure { snapshots }

instance encodeSnapshotSaveRequest :: EncodeJson SnapshotSaveRequest where
  encodeJson req = encodeJson
    { trigger: req.trigger
    , description: req.description
    }

instance decodeSnapshotSaveResponse :: DecodeJson SnapshotSaveResponse where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    success <- obj .: "success"
    pure { id, success }

instance encodeSnapshotRestoreRequest :: EncodeJson SnapshotRestoreRequest where
  encodeJson req = encodeJson { id: req.id }

instance decodeSnapshotRestoreResponse :: DecodeJson SnapshotRestoreResponse where
  decodeJson json = do
    obj <- decodeJson json
    success <- obj .: "success"
    pure { success }

instance encodeSnapshotGetRequest :: EncodeJson SnapshotGetRequest where
  encodeJson req = encodeJson { id: req.id }

instance decodeFileContextEntry :: DecodeJson FileContextEntry where
  decodeJson json = do
    obj <- decodeJson json
    path <- obj .: "path"
    tokens <- obj .: "tokens"
    language <- obj .: "language"
    pure { path, tokens, language }

instance decodeSnapshotGetState :: DecodeJson SnapshotGetState where
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

instance decodeSnapshotGetResponse :: DecodeJson SnapshotGetResponse where
  decodeJson json = do
    obj <- decodeJson json
    id <- obj .: "id"
    timestamp <- obj .: "timestamp"
    description <- obj .:? "description"
    state <- obj .: "state"
    pure { id, timestamp, description, state }

--------------------------------------------------------------------------------
-- | Session Operations
--------------------------------------------------------------------------------

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
        Right r -> pure $ Right r

--------------------------------------------------------------------------------
-- | Snapshot Operations
--------------------------------------------------------------------------------

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
        Right r -> pure $ Right r

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
        Right r -> pure $ Right r

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
        Right r -> pure $ Right r

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
        Right r -> pure $ Right r
