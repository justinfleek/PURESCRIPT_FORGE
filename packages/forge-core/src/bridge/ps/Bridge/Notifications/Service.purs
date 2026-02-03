-- | Notification Service - User Notification Management and Broadcasting
-- |
-- | **What:** Provides a service for creating, managing, and broadcasting notifications
-- |         to WebSocket clients. Supports multiple notification types (toast, banner,
-- |         inline, silent) and levels (success, info, warning, error).
-- | **Why:** Centralizes notification management, ensuring consistent notification
-- |         delivery to all connected clients. Provides convenience functions for
-- |         common notification types.
-- | **How:** Uses WebSocket manager to broadcast notifications to all connected clients.
-- |         Maintains notification state and provides dismiss functionality.
-- |
-- | **Dependencies:**
-- | - `Bridge.WebSocket.Manager`: For broadcasting notifications
-- | - `Bridge.FFI.Node.Pino`: Structured logging
-- |
-- | **Mathematical Foundation:**
-- | - **Notification ID:** Each notification has a unique ID. IDs are never reused.
-- | - **Broadcast Invariant:** Notifications are broadcast to all authenticated clients
-- |   synchronously.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Bridge.Notifications.Service as Notifications
-- |
-- | -- Create service
-- | service <- Notifications.create wsManager logger
-- |
-- | -- Send notification
-- | Notifications.success service "Operation completed" (Just "Details...")
-- | Notifications.error service "Operation failed" (Just "Error details...")
-- |
-- | -- Dismiss notification
-- | Notifications.dismiss service "notification-id"
-- | ```
module Bridge.Notifications.Service where

import Prelude
import Effect (Effect)
import Bridge.FFI.Node.Pino as Pino
import Bridge.WebSocket.Manager (WebSocketManager)

-- | Opaque Notification Service type
foreign import data NotificationService :: Type

-- | Notification type
type Notification =
  { id :: String
  , type_ :: NotificationType
  , level :: NotificationLevel
  , title :: String
  , message :: Maybe String
  , group :: Maybe String
  , actions :: Array NotificationAction
  , timestamp :: String
  }

data NotificationType = Toast | Banner | Inline | Silent

derive instance eqNotificationType :: Eq NotificationType

data NotificationLevel = Success | Info | Warning | Error

derive instance eqNotificationLevel :: Eq NotificationLevel

type NotificationAction =
  { label :: String
  , action :: String
  }

-- | Create notification service
foreign import create :: WebSocketManager -> Pino.Logger -> Effect NotificationService

-- | Notify
foreign import notify :: NotificationService -> String -> Effect Unit -- Takes JSON string

foreign import encodeNotification :: { type_ :: String, level :: String, title :: String, message :: Maybe String } -> String

-- | Success notification
success :: NotificationService -> String -> Maybe String -> Effect Unit
success service title message = do
  notify service (encodeNotification { type_: "toast", level: "success", title, message })

-- | Error notification - Send error toast notification
-- |
-- | **Purpose:** Sends an error-level toast notification to all clients.
-- | **Parameters:**
-- | - `service`: Notification service
-- | - `title`: Notification title
-- | - `message`: Optional notification message
-- | **Returns:** Unit
-- | **Side Effects:** Broadcasts notification via WebSocket
error :: NotificationService -> String -> Maybe String -> Effect Unit
error service title message = do
  notify service (encodeNotification { type_: "toast", level: "error", title, message })

-- | Warn notification
warn :: NotificationService -> String -> Maybe String -> Effect Unit
warn service title message = do
  notify service (encodeNotification { type_: "toast", level: "warning", title, message })

-- | Info notification - Send info toast notification
-- |
-- | **Purpose:** Sends an info-level toast notification to all clients.
-- | **Parameters:**
-- | - `service`: Notification service
-- | - `title`: Notification title
-- | - `message`: Optional notification message
-- | **Returns:** Unit
-- | **Side Effects:** Broadcasts notification via WebSocket
info :: NotificationService -> String -> Maybe String -> Effect Unit
info service title message = do
  notify service (encodeNotification { type_: "toast", level: "info", title, message })

-- | Notify low balance - Send balance warning notification
-- |
-- | **Purpose:** Sends a notification when Venice Diem balance is low. Uses warning
-- |             level for balance < 1.0, info level for balance < 5.0.
-- | **Parameters:**
-- | - `service`: Notification service
-- | - `diem`: Current Diem balance
-- | **Returns:** Unit
-- | **Side Effects:** Broadcasts notification via WebSocket (if balance is low)
-- |
-- | **Thresholds:**
-- | - Balance < 1.0: Warning notification
-- | - Balance < 5.0: Info notification
-- | - Balance >= 5.0: No notification
notifyLowBalance :: NotificationService -> Number -> Effect Unit
notifyLowBalance service diem = do
  if diem < 1.0 then
    warn service "Low Venice Balance" (Just ("Diem balance: " <> show diem))
  else if diem < 5.0 then
    info service "Venice Balance" (Just ("Diem balance: " <> show diem))
  else
    pure unit

-- | Dismiss notification
foreign import dismiss :: NotificationService -> String -> Effect Unit

-- | Dismiss all notifications
foreign import dismissAll :: NotificationService -> Effect Unit
