-- | Notification Service - User Notification Management and Broadcasting
-- | Supports multiple notification types (toast, banner, inline, silent)
-- | and levels (success, info, warning, error)
module Bridge.Notifications.Service where

import Prelude
import Effect (Effect)
import Data.Maybe (Maybe(..))
import Bridge.FFI.Node.Pino as Pino
import Bridge.WebSocket.Manager (WebSocketManager)

-- | Opaque Notification Service type
foreign import data NotificationService :: Type

-- | Notification type
data NotificationType = Toast | Banner | Inline | Silent

derive instance eqNotificationType :: Eq NotificationType

-- | Notification level
data NotificationLevel = Success | NInfo | NWarning | NError

derive instance eqNotificationLevel :: Eq NotificationLevel

-- | Notification action
type NotificationAction =
  { label :: String
  , action :: String
  }

-- | FFI declarations (top-level)
foreign import create :: WebSocketManager -> Pino.Logger -> Effect NotificationService
foreign import notify :: NotificationService -> String -> Effect Unit
foreign import encodeNotification :: { type_ :: String, level :: String, title :: String, message :: Maybe String } -> String
foreign import dismiss :: NotificationService -> String -> Effect Unit
foreign import dismissAll :: NotificationService -> Effect Unit

-- | Success notification
success :: NotificationService -> String -> Maybe String -> Effect Unit
success service title message =
  notify service (encodeNotification { type_: "toast", level: "success", title, message })

-- | Error notification
error :: NotificationService -> String -> Maybe String -> Effect Unit
error service title message =
  notify service (encodeNotification { type_: "toast", level: "error", title, message })

-- | Warning notification
warn :: NotificationService -> String -> Maybe String -> Effect Unit
warn service title message =
  notify service (encodeNotification { type_: "toast", level: "warning", title, message })

-- | Info notification
info :: NotificationService -> String -> Maybe String -> Effect Unit
info service title message =
  notify service (encodeNotification { type_: "toast", level: "info", title, message })

-- | Notify low balance
notifyLowBalance :: NotificationService -> Number -> Effect Unit
notifyLowBalance service diem =
  if diem < 1.0 then
    warn service "Low Venice Balance" (Just ("Diem balance: " <> show diem))
  else if diem < 5.0 then
    info service "Venice Balance" (Just ("Diem balance: " <> show diem))
  else
    pure unit
