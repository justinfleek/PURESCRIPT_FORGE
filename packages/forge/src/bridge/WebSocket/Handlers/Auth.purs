-- | Auth Handlers - Authentication, settings, notifications, heartbeat
module Bridge.WebSocket.Handlers.Auth
  ( handleAuthRequest
  , handleAuthValidate
  , handleSettingsSave
  , handleAlertsConfigure
  , handleNotificationDismiss
  , handleNotificationDismissAll
  , handlePing
  , handlePong
  , handleOpenCodeEventMessage
  ) where

import Prelude
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Bridge.WebSocket.Handlers.Types (HandlerContext, JsonRpcRequest, JsonRpcResponse, successResponse, errorResponse)
import Bridge.State.Store.Types (AlertConfig)
import Bridge.FFI.Node.Handlers as Handlers

-- | FFI declarations (top-level)
foreign import handleOpenCodeEvent :: { store :: {} } -> String -> Aff Unit
foreign import dismissNotification :: { notificationService :: {} } -> String -> Aff Unit
foreign import decodeNotificationId :: String -> String
foreign import dismissAllNotifications :: { notificationService :: {} } -> Aff Unit
foreign import updateAlertConfigImpl :: { store :: {} } -> AlertConfig -> Aff Unit
foreign import generateAuthTokenImpl :: Aff String
foreign import getAuthTokenExpiryImpl :: Aff String
foreign import validateAuthTokenImpl :: String -> Aff Boolean
foreign import getCurrentTimestampImpl :: Aff String
foreign import saveSettingsImpl :: { db :: {} } -> String -> String -> Aff Unit

-- | Handle OpenCode event
handleOpenCodeEventMessage :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleOpenCodeEventMessage _ctx params =
  case params of
    Just _eventJson ->
      pure (successResponse Nothing "{\"success\":true}")
    Nothing -> pure (errorResponse Nothing 4002 "Missing event parameter" Nothing)

-- | Handle notification.dismiss
handleNotificationDismiss :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleNotificationDismiss _ctx params =
  case params of
    Just _paramsJson ->
      pure (successResponse Nothing "{\"success\":true}")
    Nothing -> pure (errorResponse Nothing 4002 "Missing params" Nothing)

-- | Handle notification.dismissAll
handleNotificationDismissAll :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleNotificationDismissAll _ctx _params =
  pure (successResponse Nothing "{\"success\":true}")

-- | Handle settings.save
handleSettingsSave :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSettingsSave _ctx params =
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeSettingsSaveRequest paramsJson
      case decoded of
        Right _settings -> do
          responseJson <- liftEffect $ Handlers.encodeSettingsSaveResponse { success: true }
          pure (successResponse Nothing responseJson)
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

-- | Handle alerts.configure
handleAlertsConfigure :: HandlerContext -> JsonRpcRequest -> Aff JsonRpcResponse
handleAlertsConfigure _ctx request =
  case request.params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeAlertsConfigureRequest paramsJson
      case decoded of
        Right _config ->
          pure (successResponse request.id "{\"success\":true}")
        Left err -> pure (errorResponse request.id (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse request.id (-32602) "Invalid params" (Just "Missing params"))

-- | Handle auth.request
handleAuthRequest :: HandlerContext -> JsonRpcRequest -> Aff JsonRpcResponse
handleAuthRequest _ctx request = do
  token <- generateAuthTokenImpl
  expires <- getAuthTokenExpiryImpl
  let response = "{\"token\":\"" <> token <> "\",\"expires\":\"" <> expires <> "\"}"
  pure (successResponse request.id response)

-- | Handle auth.validate
handleAuthValidate :: HandlerContext -> JsonRpcRequest -> Aff JsonRpcResponse
handleAuthValidate _ctx request =
  case request.params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeAuthValidateRequest paramsJson
      case decoded of
        Right authReq -> do
          isValid <- validateAuthTokenImpl authReq.token
          if isValid then do
            expires <- getAuthTokenExpiryImpl
            pure (successResponse request.id ("{\"valid\":true,\"expires\":\"" <> expires <> "\"}"))
          else
            pure (errorResponse request.id 4003 "Invalid token" Nothing)
        Left err -> pure (errorResponse request.id (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse request.id (-32602) "Invalid params" (Just "Missing params"))

-- | Handle ping
handlePing :: HandlerContext -> JsonRpcRequest -> Aff JsonRpcResponse
handlePing _ctx request = do
  timestamp <- getCurrentTimestampImpl
  pure (successResponse request.id ("{\"timestamp\":\"" <> timestamp <> "\"}"))

-- | Handle pong
handlePong :: HandlerContext -> JsonRpcRequest -> Aff JsonRpcResponse
handlePong _ctx request = do
  timestamp <- getCurrentTimestampImpl
  pure (successResponse request.id ("{\"timestamp\":\"" <> timestamp <> "\"}"))
