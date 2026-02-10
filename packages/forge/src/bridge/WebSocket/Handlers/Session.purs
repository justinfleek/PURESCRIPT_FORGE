-- | Session Handlers - Session and snapshot management
module Bridge.WebSocket.Handlers.Session
  ( handleSessionNew
  , handleSessionExport
  , handleSnapshotSave
  , handleSnapshotRestore
  , handleSnapshotList
  , handleSnapshotGet
  , handleStateGet
  ) where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect (Effect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Bridge.WebSocket.Handlers.Types (HandlerContext, JsonRpcResponse, successResponse, errorResponse)
import Bridge.FFI.Haskell.Database as DB
import Bridge.FFI.Node.Handlers as Handlers

-- | FFI declarations (top-level)
foreign import getState :: { store :: {} } -> Effect String
foreign import decodeSnapshotSaveRequest :: String -> Effect (Either String { trigger :: String, description :: Maybe String })
foreign import decodeSnapshotRestoreRequest :: String -> Effect (Either String { id :: String })
foreign import decodeSnapshotListRequest :: Maybe String -> Effect (Either String { limit :: Maybe Int, offset :: Maybe Int })
foreign import decodeSnapshotGetRequest :: String -> Effect (Either String { id :: String })
foreign import decodeSessionExportRequest :: String -> Effect (Either String { sessionId :: String })
foreign import generateSnapshotId :: Effect String
foreign import computeStateHash :: String -> Effect String
foreign import getCurrentTimestamp :: Effect String
foreign import encodeSnapshots :: Array String -> Effect String
foreign import encodeSnapshotGetResponse :: { id :: String, timestamp :: String, description :: Maybe String, state :: String } -> Effect String
foreign import encodeSessionExport :: String -> Effect String

-- | Handle state.get
handleStateGet :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleStateGet _ctx _params = do
  stateJson <- liftEffect $ getState {}
  pure (successResponse Nothing stateJson)

-- | Handle session.new
handleSessionNew :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSessionNew _ctx params =
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeSessionNewRequest paramsJson
      case decoded of
        Right _request -> do
          responseJson <- liftEffect $ Handlers.encodeSessionNewResponse { sessionId: "new-session", success: true }
          pure (successResponse Nothing responseJson)
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

-- | Handle session.export
handleSessionExport :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSessionExport ctx params =
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ decodeSessionExportRequest paramsJson
      case decoded of
        Right request -> do
          sessionsJson <- DB.getSessionsBySessionId ctx.db request.sessionId
          case sessionsJson of
            Left err -> pure (errorResponse Nothing (-32602) "Session lookup failed" (Just err))
            Right json -> do
              exportData <- liftEffect $ encodeSessionExport json
              pure (successResponse Nothing exportData)
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

-- | Handle snapshot.save
handleSnapshotSave :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSnapshotSave ctx params =
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ decodeSnapshotSaveRequest paramsJson
      case decoded of
        Right request -> do
          stateJson <- liftEffect $ getState {}
          stateHash <- liftEffect $ computeStateHash stateJson
          snapshotId <- liftEffect $ generateSnapshotId
          result <- DB.saveSnapshot ctx.db stateHash stateJson (Just request.trigger) request.description
          case result of
            Right _ ->
              pure (successResponse Nothing ("{\"id\":\"" <> snapshotId <> "\",\"success\":true}"))
            Left err ->
              pure (errorResponse Nothing (-32603) "Failed to save snapshot" (Just err))
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

-- | Handle snapshot.restore
handleSnapshotRestore :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSnapshotRestore ctx params =
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ decodeSnapshotRestoreRequest paramsJson
      case decoded of
        Right request -> do
          snapshotResult <- DB.getSnapshot ctx.db request.id
          case snapshotResult of
            Right _snapJson ->
              pure (successResponse Nothing ("{\"id\":\"" <> request.id <> "\",\"success\":true}"))
            Left err ->
              pure (errorResponse Nothing (-32602) "Snapshot not found" (Just err))
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

-- | Handle snapshot.list
handleSnapshotList :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSnapshotList ctx params = do
  decoded <- liftEffect $ decodeSnapshotListRequest params
  case decoded of
    Right request -> do
      snapshotsResult <- DB.listSnapshots ctx.db request.limit request.offset
      case snapshotsResult of
        Right snapshots -> do
          snapshotsJson <- liftEffect $ encodeSnapshots [snapshots]
          pure (successResponse Nothing snapshotsJson)
        Left err ->
          pure (errorResponse Nothing (-32603) "Failed to list snapshots" (Just err))
    Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))

-- | Handle snapshot.get
handleSnapshotGet :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSnapshotGet ctx params =
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ decodeSnapshotGetRequest paramsJson
      case decoded of
        Right request -> do
          snapshotResult <- DB.getSnapshot ctx.db request.id
          case snapshotResult of
            Right snapJson -> do
              responseJson <- liftEffect $ encodeSnapshotGetResponse
                { id: request.id, timestamp: "", description: Nothing, state: snapJson }
              pure (successResponse Nothing responseJson)
            Left err ->
              pure (errorResponse Nothing (-32602) "Snapshot not found" (Just err))
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))
