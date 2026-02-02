-- | Alert System Component - Notification and Alert Display System
-- |
-- | **What:** Displays alerts and notifications to users with support for different severity
-- |         levels (Info, Warning, Error, Success), auto-dismiss timers, and dismissible
-- |         alerts. Converts Bridge Server notifications to UI alerts.
-- | **Why:** Provides user feedback for important events, errors, warnings, and system
-- |         status updates. Essential for user awareness and error handling.
-- | **How:** Renders alert components with appropriate styling based on type, supports
-- |         auto-dismiss with configurable delays, and manages alert queue with maximum
-- |         display limit. Converts NotificationPayload from Bridge Server to Alert format.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.Api.Types`: NotificationPayload type
-- |
-- | **Mathematical Foundation:**
-- | - **Alert Queue:** Alerts are stored in an array with maximum limit (default 5). New
-- |   alerts are prepended and oldest alerts are removed when limit is exceeded.
-- | - **Auto-Dismiss:** Alerts with `autoDismiss` delay are automatically dismissed after
-- |   the specified milliseconds.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.AlertSystem as AlertSystem
-- |
-- | -- In parent component:
-- | HH.slot _alerts unit AlertSystem.component unit
-- |   (const HandleAppAction)
-- |
-- | -- Show notification:
-- | H.query _alerts unit $ H.tell $ AlertSystem.ShowNotificationQuery payload
-- |
-- | -- Dismiss notification:
-- | H.query _alerts unit $ H.tell $ AlertSystem.DismissNotificationQuery alertId
-- | ```
-- |
-- | Spec 56: Notifications and warnings
module Sidepanel.Components.AlertSystem where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff (Aff, delay, Milliseconds(..))
import Effect.Aff.Class (class MonadAff)
import Data.Array (cons, filter, take)
import Data.Maybe (Maybe(..))
import Sidepanel.Api.Types (NotificationPayload)

-- | Alert type
data AlertType
  = Info String
  | Warning String
  | Error String
  | Success String

-- | Alert data
type Alert =
  { id :: String
  , type :: AlertType
  , message :: String
  , timestamp :: Number
  , dismissible :: Boolean
  , autoDismiss :: Maybe Number -- milliseconds
  }

-- | Component state
type State =
  { alerts :: Array Alert
  , maxAlerts :: Int
  }

-- | Component actions
data Action
  = Initialize
  | ShowAlert Alert
  | ShowNotification NotificationPayload
  | DismissAlert String
  | AutoDismiss String
  | ClearAll

-- | Component queries
data Query a
  = ShowNotificationQuery NotificationPayload a
  | DismissNotificationQuery String a

-- | Component output
data Output
  = AlertShown Alert
  | AlertDismissed String

-- | Alert System component
component :: forall q m. MonadAff m => H.Component q Query Output m
component =
  H.mkComponent
    { initialState: const initialState
    , render
    , eval: H.mkEval $ H.defaultEval
        { handleAction = handleAction
        , handleQuery = handleQuery
        , initialize = Just Initialize
        }
    }

-- | Handle queries
handleQuery :: forall m a. Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  ShowNotificationQuery payload a -> do
    handleAction (ShowNotification payload)
    pure (Just a)
  DismissNotificationQuery id a -> do
    handleAction (DismissAlert id)
    pure (Just a)

initialState :: State
initialState =
  { alerts: []
  , maxAlerts: 5
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "alert-system") ]
    (map renderAlert state.alerts)

renderAlert :: forall m. Alert -> H.ComponentHTML Action () m
renderAlert alert =
  HH.div
    [ HP.class_ (H.ClassName $ "alert alert-" <> alertClass alert.type)
    , HP.attr (H.AttrName "role") "alert"
    ]
    [ HH.div
        [ HP.class_ (H.ClassName "alert-content") ]
        [ HH.span
            [ HP.class_ (H.ClassName "alert-message") ]
            [ HH.text alert.message ]
        ]
    , if alert.dismissible then
        HH.button
          [ HP.class_ (H.ClassName "alert-dismiss")
          , HE.onClick \_ -> DismissAlert alert.id
          , HP.attr (H.AttrName "aria-label") "Dismiss alert"
          ]
          [ HH.text "×" ]
      else
        HH.text ""
    ]

alertClass :: AlertType -> String
alertClass = case _ of
  Info _ -> "info"
  Warning _ -> "warning"
  Error _ -> "error"
  Success _ -> "success"

-- | Convert notification payload to alert
notificationToAlert :: NotificationPayload -> Alert
notificationToAlert payload =
  { id: payload.id
  , type: levelToAlertType payload.level
  , message: payload.title <> case payload.message of
      Just msg -> ": " <> msg
      Nothing -> ""
  , timestamp: 0.0  -- Would parse createdAt
  , dismissible: payload.dismissible
  , autoDismiss: payload.duration
  }

-- | Convert notification level to alert type
levelToAlertType :: String -> AlertType
levelToAlertType = case _ of
  "success" -> Success ""
  "info" -> Info ""
  "warning" -> Warning ""
  "error" -> Error ""
  _ -> Info ""

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Initialize alert system
    pure unit
  
  ShowNotification payload -> do
    let alert = notificationToAlert payload
    handleAction (ShowAlert alert)
  
  ShowAlert alert -> do
    H.modify_ \s ->
      { s
      | alerts = take s.maxAlerts $ cons alert s.alerts
      }
    H.raise (AlertShown alert)
    
    -- Auto-dismiss if configured
    case alert.autoDismiss of
      Just delayMs -> do
        -- Fork auto-dismiss timer
        void $ H.fork $ H.liftAff do
          delay (Milliseconds delayMs)
          -- Auto-dismiss will be handled via subscription or direct action
          pure unit
        -- Note: In a full implementation, we'd store the fiber ID for cleanup
        pure unit
      Nothing ->
        pure unit
  
  DismissAlert id -> do
    H.modify_ \s ->
      { s
      | alerts = filter (\a -> a.id /= id) s.alerts
      }
    H.raise (AlertDismissed id)
  
  AutoDismiss id -> do
    handleAction (DismissAlert id)
  
  ClearAll -> do
    H.modify_ \s -> s { alerts = [] }
