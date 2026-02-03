-- | Notification context - manages app notifications
-- | Migrated from: forge-dev/packages/app/src/context/notification.tsx
module App.Context.Notification
  ( Notification(..)
  , NotificationType(..)
  , NotificationStore
  , mkNotificationStore
  , pruneNotifications
  , appendNotification
  , getSessionNotifications
  , getProjectNotifications
  , markSessionViewed
  , markProjectViewed
  , maxNotifications
  , notificationTtlMs
  ) where

import Prelude

import Data.Array (filter, snoc)
import Data.Maybe (Maybe(..))
import Foreign.Object (Object)
import Foreign.Object as Object

-- | Notification type discriminator
data NotificationType
  = TurnComplete
  | Error

derive instance eqNotificationType :: Eq NotificationType

instance showNotificationType :: Show NotificationType where
  show TurnComplete = "turn-complete"
  show Error = "error"

-- | Error details
type ErrorDetails =
  { message :: Maybe String
  , code :: Maybe String
  }

-- | Notification record
type Notification =
  { notificationType :: NotificationType
  , directory :: Maybe String
  , session :: Maybe String
  , metadata :: Maybe String  -- JSON string for arbitrary metadata
  , time :: Number
  , viewed :: Boolean
  , error :: Maybe ErrorDetails
  }

-- | Notification store state
type NotificationStore =
  { list :: Array Notification
  }

-- | Maximum notifications to keep
maxNotifications :: Int
maxNotifications = 500

-- | Notification time-to-live (30 days in milliseconds)
notificationTtlMs :: Number
notificationTtlMs = 1000.0 * 60.0 * 60.0 * 24.0 * 30.0

-- | Create initial notification store
mkNotificationStore :: NotificationStore
mkNotificationStore = { list: [] }

-- | Prune old notifications
pruneNotifications :: Number -> Array Notification -> Array Notification
pruneNotifications now list =
  let
    cutoff = now - notificationTtlMs
    pruned = filter (\n -> n.time >= cutoff) list
    len = arrayLength pruned
  in
    if len <= maxNotifications
    then pruned
    else drop (len - maxNotifications) pruned
  where
    arrayLength :: forall a. Array a -> Int
    arrayLength arr = go 0 arr
      where
        go acc [] = acc
        go acc (_ : rest) = go (acc + 1) rest
    
    drop :: forall a. Int -> Array a -> Array a
    drop n arr =
      if n <= 0 then arr
      else case arr of
        [] -> []
        (_ : rest) -> drop (n - 1) rest

-- | Append a notification
appendNotification :: Number -> Notification -> NotificationStore -> NotificationStore
appendNotification now notification store =
  let
    newList = snoc store.list notification
    pruned = pruneNotifications now newList
  in
    { list: pruned }

-- | Get notifications for a session
getSessionNotifications :: String -> NotificationStore -> { all :: Array Notification, unseen :: Array Notification }
getSessionNotifications sessionId store =
  let
    all = filter (\n -> n.session == Just sessionId) store.list
    unseen = filter (\n -> not n.viewed) all
  in
    { all, unseen }

-- | Get notifications for a project
getProjectNotifications :: String -> NotificationStore -> { all :: Array Notification, unseen :: Array Notification }
getProjectNotifications directory store =
  let
    all = filter (\n -> n.directory == Just directory) store.list
    unseen = filter (\n -> not n.viewed) all
  in
    { all, unseen }

-- | Mark all session notifications as viewed
markSessionViewed :: String -> NotificationStore -> NotificationStore
markSessionViewed sessionId store =
  { list: map markIfMatch store.list }
  where
    markIfMatch n =
      if n.session == Just sessionId
      then n { viewed = true }
      else n

-- | Mark all project notifications as viewed
markProjectViewed :: String -> NotificationStore -> NotificationStore
markProjectViewed directory store =
  { list: map markIfMatch store.list }
  where
    markIfMatch n =
      if n.directory == Just directory
      then n { viewed = true }
      else n
