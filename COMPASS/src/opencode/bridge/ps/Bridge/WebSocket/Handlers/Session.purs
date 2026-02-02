{-|
Module      : Bridge.WebSocket.Handlers.Session
Description : Session and snapshot management handlers
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Session Handlers

JSON-RPC handlers for session management (create, export) and
snapshot operations (save, restore, list, get).

== Error Codes

| Code   | Meaning             |
|--------|---------------------|
| -32602 | Invalid params      |

== Snapshot Structure

Snapshots capture:
- Balance state
- Session state
- Proof state
- Usage metrics
- File context
-}
module Bridge.WebSocket.Handlers.Session
  ( -- * Session Handlers
    handleSessionNew
  , handleSessionExport
    -- * Snapshot Handlers
  , handleSnapshotSave
  , handleSnapshotRestore
  , handleSnapshotList
  , handleSnapshotGet
    -- * State Handlers
  , handleStateGet
  ) where

import Prelude

import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect (Effect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)

import Bridge.WebSocket.Handlers.Types (HandlerContext, JsonRpcResponse, successResponse, errorResponse)
import Bridge.State.Store (StateStore, SessionState)
import Bridge.FFI.Haskell.Database as DB
import Bridge.FFI.Node.Handlers as Handlers
import Bridge.FFI.Node.Process as Process

-- ============================================================================
-- FFI
-- ============================================================================

foreign import getState :: StateStore -> Effect AppState
foreign import encodeState :: AppState -> Effect String
foreign import decodeSnapshotSaveRequest :: String -> Effect (Either String { trigger :: String, description :: Maybe String })
foreign import decodeSnapshotRestoreRequest :: String -> Effect (Either String { id :: String })
foreign import decodeSnapshotListRequest :: Maybe String -> Effect (Either String { limit :: Maybe Int, offset :: Maybe Int })
foreign import decodeSnapshotGetRequest :: String -> Effect (Either String { id :: String })
foreign import decodeSessionExportRequest :: String -> Effect (Either String { sessionId :: String })
foreign import generateSnapshotId :: Effect String
foreign import computeStateHash :: String -> Effect String
foreign import getCurrentTimestamp :: Effect String
foreign import parseSnapshotData :: String -> Effect SnapshotData
foreign import encodeSnapshots :: Array String -> Effect String
foreign import encodeSnapshotGetResponse :: SnapshotGetResponse -> Effect String
foreign import getFileContextForSnapshot :: StateStore -> Effect (Array FileContextEntry)
foreign import enrichStateWithFileContext :: String -> Array FileContextEntry -> Effect String
foreign import parseSessions :: String -> Effect (Array SessionState)
foreign import encodeSessionExport :: SessionState -> Effect String
foreign import updateBalance :: StateStore -> BalanceState -> Effect Unit
foreign import updateSession :: StateStore -> SessionState -> Effect Unit
foreign import clearSession :: StateStore -> Effect Unit
foreign import updateProof :: StateStore -> ProofState -> Effect Unit
foreign import updateMetrics :: StateStore -> UsageMetrics -> Effect Unit

-- Type aliases for FFI
type AppState = {}
type BalanceState = {}
type ProofState = {}
type UsageMetrics = {}
type FileContextEntry = { path :: String, tokens :: Int, language :: String }
type SnapshotData =
  { balance :: Maybe BalanceState
  , session :: Maybe SessionState
  , proof :: Maybe ProofState
  , metrics :: Maybe UsageMetrics
  , fileContext :: Array FileContextEntry
  , timestamp :: String
  , description :: Maybe String
  }
type SnapshotGetResponse =
  { id :: String
  , timestamp :: String
  , description :: Maybe String
  , state :: SnapshotData
  }

-- ============================================================================
-- STATE HANDLERS
-- ============================================================================

{-| Handle state.get - Get current application state. -}
handleStateGet :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleStateGet ctx _params = do
  state <- liftEffect $ getState ctx.store
  encoded <- liftEffect $ encodeState state
  pure (successResponse Nothing encoded)

-- ============================================================================
-- SESSION HANDLERS
-- ============================================================================

{-| Handle session.new - Create new session. -}
handleSessionNew :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSessionNew ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeSessionNewRequest paramsJson
      case decoded of
        Right request -> do
          sessionId <- liftEffect Process.generateSessionId
          timestamp <- liftEffect $ getCurrentTimestamp
          startedAt <- liftEffect $ Process.parseDateTime timestamp
          
          let newSession :: SessionState =
                { id: sessionId
                , promptTokens: 0
                , completionTokens: 0
                , totalTokens: 0
                , cost: 0.0
                , model: fromMaybe "default" request.model
                , provider: fromMaybe "venice" request.provider
                , messageCount: 0
                , startedAt: startedAt
                , updatedAt: startedAt
                }
          
          liftEffect $ updateSession ctx.store newSession
          liftEffect $ DB.saveSession ctx.db sessionId timestamp 0 0 0.0 
            (fromMaybe "default" request.model) (fromMaybe "venice" request.provider) timestamp Nothing
          
          responseJson <- liftEffect $ Handlers.encodeSessionNewResponse { sessionId, success: true }
          pure (successResponse Nothing responseJson)
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

{-| Handle session.export - Export session data. -}
handleSessionExport :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSessionExport ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ decodeSessionExportRequest paramsJson
      case decoded of
        Right request -> do
          sessionsJson <- DB.getSessionsBySessionId ctx.db request.sessionId
          sessions <- liftEffect $ parseSessions sessionsJson
          case sessions of
            [] -> pure (errorResponse Nothing (-32602) "Session not found" (Just ("Session ID: " <> request.sessionId)))
            (session:_) -> do
              exportData <- liftEffect $ encodeSessionExport session
              pure (successResponse Nothing exportData)
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

-- ============================================================================
-- SNAPSHOT HANDLERS
-- ============================================================================

{-| Handle snapshot.save - Save application state snapshot. -}
handleSnapshotSave :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSnapshotSave ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ decodeSnapshotSaveRequest paramsJson
      case decoded of
        Right request -> do
          state <- liftEffect $ getState ctx.store
          stateJson <- liftEffect $ encodeState state
          stateHash <- liftEffect $ computeStateHash stateJson
          fileContext <- liftEffect $ getFileContextForSnapshot ctx.store
          enrichedStateJson <- liftEffect $ enrichStateWithFileContext stateJson fileContext
          snapshotId <- liftEffect $ generateSnapshotId
          timestamp <- liftEffect $ getCurrentTimestamp
          
          liftEffect $ DB.saveSnapshot ctx.db snapshotId timestamp stateHash enrichedStateJson 
            (Just request.trigger) request.description
          
          pure (successResponse Nothing ("{\"id\":\"" <> snapshotId <> "\",\"success\":true}"))
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

{-| Handle snapshot.restore - Restore application state from snapshot. -}
handleSnapshotRestore :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSnapshotRestore ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ decodeSnapshotRestoreRequest paramsJson
      case decoded of
        Right request -> do
          snapshotJson <- DB.getSnapshot ctx.db request.id
          case snapshotJson of
            Just snapJson -> do
              stateData <- liftEffect $ parseSnapshotData snapJson
              
              case stateData.balance of
                Just balance -> liftEffect $ updateBalance ctx.store balance
                Nothing -> pure unit
              
              case stateData.session of
                Just session -> liftEffect $ updateSession ctx.store session
                Nothing -> liftEffect $ clearSession ctx.store
              
              case stateData.proof of
                Just proof -> liftEffect $ updateProof ctx.store proof
                Nothing -> pure unit
              
              case stateData.metrics of
                Just metrics -> liftEffect $ updateMetrics ctx.store metrics
                Nothing -> pure unit
              
              pure (successResponse Nothing ("{\"id\":\"" <> request.id <> "\",\"success\":true}"))
            Nothing -> pure (errorResponse Nothing (-32602) "Snapshot not found" (Just ("Snapshot ID: " <> request.id)))
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

{-| Handle snapshot.list - List saved snapshots with pagination. -}
handleSnapshotList :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSnapshotList ctx params = do
  decoded <- liftEffect $ decodeSnapshotListRequest params
  case decoded of
    Right request -> do
      snapshots <- liftEffect $ DB.listSnapshots ctx.db request.limit request.offset
      snapshotsJson <- liftEffect $ encodeSnapshots snapshots
      pure (successResponse Nothing snapshotsJson)
    Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))

{-| Handle snapshot.get - Get a specific snapshot. -}
handleSnapshotGet :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSnapshotGet ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ decodeSnapshotGetRequest paramsJson
      case decoded of
        Right request -> do
          snapshotJson <- DB.getSnapshot ctx.db request.id
          case snapshotJson of
            Just snapJson -> do
              stateData <- liftEffect $ parseSnapshotData snapJson
              responseJson <- liftEffect $ encodeSnapshotGetResponse
                { id: request.id
                , timestamp: stateData.timestamp
                , description: stateData.description
                , state: stateData
                }
              pure (successResponse Nothing responseJson)
            Nothing -> pure (errorResponse Nothing (-32602) "Snapshot not found" (Just ("Snapshot ID: " <> request.id)))
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))
