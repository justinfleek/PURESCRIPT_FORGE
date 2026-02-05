{-|
Module      : Bridge.WebSocket.Handlers.Auth
Description : Authentication and settings handlers
= Auth Handlers

JSON-RPC handlers for authentication, settings, notifications,
and heartbeat operations.

== Error Codes

| Code   | Meaning          |
|--------|------------------|
| 4002   | Missing params   |
| 4003   | Invalid token    |
| -32602 | Invalid params   |

== Heartbeat Protocol

The server sends periodic "ping" messages. Clients must respond
with "pong" to maintain connection health.
-}
module Bridge.WebSocket.Handlers.Auth
  ( -- * Auth Handlers
    handleAuthRequest
  , handleAuthValidate
    -- * Settings Handlers
  , handleSettingsSave
  , handleAlertsConfigure
    -- * Notification Handlers
  , handleNotificationDismiss
  , handleNotificationDismissAll
    -- * Heartbeat Handlers
  , handlePing
  , handlePong
    -- * OpenCode Event Handler
  , handleOpenCodeEventMessage
  ) where

import Prelude

import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect (Effect)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Argonaut as AC
import Data.Argonaut.Encode (encodeJson)

import Bridge.WebSocket.Handlers.Types 
  ( HandlerContext
  , JsonRpcRequest
  , JsonRpcResponse
  , successResponse
  , errorResponse
  )
import Bridge.State.Store (StateStore, AlertConfig)
import Bridge.Notifications.Service (NotificationService)
import Bridge.FFI.Haskell.Database as DB
import Bridge.FFI.Node.Handlers as Handlers

-- ============================================================================
-- FFI
-- ============================================================================

foreign import handleOpenCodeEvent :: StateStore -> String -> Effect Unit
foreign import dismissNotification :: NotificationService -> String -> Effect Unit
foreign import decodeNotificationId :: String -> Effect String
foreign import dismissAllNotifications :: NotificationService -> Effect Unit
foreign import updateAlertConfig :: StateStore -> AlertConfig -> Effect Unit
foreign import generateAuthToken :: Effect String
foreign import getAuthTokenExpiry :: Effect String
foreign import validateAuthToken :: String -> Effect Boolean
foreign import getCurrentTimestamp :: Effect String

-- ============================================================================
-- OPENCODE EVENT HANDLER
-- ============================================================================

{-| Handle OpenCode event - Process OpenCode SDK event. -}
handleOpenCodeEventMessage :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleOpenCodeEventMessage ctx params = do
  case params of
    Just eventJson -> do
      liftEffect $ handleOpenCodeEvent ctx.store eventJson
      pure (successResponse Nothing "{\"success\":true}")
    Nothing -> pure (errorResponse Nothing 4002 "Missing event parameter" Nothing)

-- ============================================================================
-- NOTIFICATION HANDLERS
-- ============================================================================

{-| Handle notification.dismiss - Dismiss a notification. -}
handleNotificationDismiss :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleNotificationDismiss ctx params = do
  case params of
    Just paramsJson -> do
      notificationId <- liftEffect $ decodeNotificationId paramsJson
      liftEffect $ dismissNotification ctx.notificationService notificationId
      pure (successResponse Nothing "{\"success\":true}")
    Nothing -> pure (errorResponse Nothing 4002 "Missing params" Nothing)

{-| Handle notification.dismissAll - Dismiss all notifications. -}
handleNotificationDismissAll :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleNotificationDismissAll ctx _params = do
  liftEffect $ dismissAllNotifications ctx.notificationService
  pure (successResponse Nothing "{\"success\":true}")

-- ============================================================================
-- SETTINGS HANDLERS
-- ============================================================================

{-| Handle settings.save - Save settings to bridge server. -}
handleSettingsSave :: HandlerContext -> Maybe String -> Aff JsonRpcResponse
handleSettingsSave ctx params = do
  case params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeSettingsSaveRequest paramsJson
      case decoded of
        Right settings -> do
          let alertConfig :: AlertConfig =
                { diemWarningPercent: settings.alerts.warningPercent
                , diemCriticalPercent: settings.alerts.criticalPercent
                , depletionWarningHours: settings.alerts.warningHours
                }
          liftEffect $ updateAlertConfig ctx.store alertConfig
          
          let settingsJson = AC.stringify $ encodeJson settings
          void $ DB.saveSettings ctx.db "sidepanel.settings" settingsJson
          
          responseJson <- liftEffect $ Handlers.encodeSettingsSaveResponse { success: true }
          pure (successResponse Nothing responseJson)
        Left err -> pure (errorResponse Nothing (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse Nothing (-32602) "Invalid params" (Just "Missing params"))

{-| Handle alerts.configure - Configure alert thresholds. -}
handleAlertsConfigure :: HandlerContext -> JsonRpcRequest -> Aff JsonRpcResponse
handleAlertsConfigure ctx request = do
  case request.params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeAlertsConfigureRequest paramsJson
      case decoded of
        Right config -> do
          let alertConfig :: AlertConfig =
                { diemWarningPercent: config.diemWarningPercent
                , diemCriticalPercent: config.diemCriticalPercent
                , depletionWarningHours: config.depletionWarningHours
                }
          liftEffect $ updateAlertConfig ctx.store alertConfig
          pure (successResponse request.id "{\"success\":true}")
        Left err -> pure (errorResponse request.id (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse request.id (-32602) "Invalid params" (Just "Missing params"))

-- ============================================================================
-- AUTH HANDLERS
-- ============================================================================

{-| Handle auth.request - Request authentication token. -}
handleAuthRequest :: HandlerContext -> JsonRpcRequest -> Aff JsonRpcResponse
handleAuthRequest _ctx request = do
  token <- liftEffect $ generateAuthToken
  expires <- liftEffect $ getAuthTokenExpiry
  let response = "{\"token\":\"" <> token <> "\",\"expires\":\"" <> expires <> "\"}"
  pure (successResponse request.id response)

{-| Handle auth.validate - Validate authentication token. -}
handleAuthValidate :: HandlerContext -> JsonRpcRequest -> Aff JsonRpcResponse
handleAuthValidate _ctx request = do
  case request.params of
    Just paramsJson -> do
      decoded <- liftEffect $ Handlers.decodeAuthValidateRequest paramsJson
      case decoded of
        Right { token } -> do
          isValid <- liftEffect $ validateAuthToken token
          if isValid then do
            expires <- liftEffect $ getAuthTokenExpiry
            let response = "{\"valid\":true,\"expires\":\"" <> expires <> "\"}"
            pure (successResponse request.id response)
          else do
            pure (errorResponse request.id 4003 "Invalid token" Nothing)
        Left err -> pure (errorResponse request.id (-32602) "Invalid params" (Just err))
    Nothing -> pure (errorResponse request.id (-32602) "Invalid params" (Just "Missing params"))

-- ============================================================================
-- HEARTBEAT HANDLERS
-- ============================================================================

{-| Handle ping - Heartbeat ping. -}
handlePing :: HandlerContext -> JsonRpcRequest -> Aff JsonRpcResponse
handlePing _ctx request = do
  timestamp <- liftEffect $ getCurrentTimestamp
  let response = "{\"timestamp\":\"" <> timestamp <> "\"}"
  pure (successResponse request.id response)

{-| Handle pong - Heartbeat pong response. -}
handlePong :: HandlerContext -> JsonRpcRequest -> Aff JsonRpcResponse
handlePong _ctx request = do
  timestamp <- liftEffect $ getCurrentTimestamp
  let response = "{\"timestamp\":\"" <> timestamp <> "\"}"
  pure (successResponse request.id response)
