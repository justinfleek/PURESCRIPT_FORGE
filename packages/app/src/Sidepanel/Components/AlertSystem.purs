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
import Effect.Aff (Aff, delay, Milliseconds(..), Fiber, killFiber, error)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Data.Array (cons, filter, take)
import Data.Maybe (Maybe(..))
import Data.Map as Map
import Data.String as String
import Sidepanel.Api.Types (NotificationPayload)

-- | Alert category - Category of alert
data AlertCategory
  = BalanceAlert
  | RateLimitAlert
  | ConnectionAlert
  | ProofAlert
  | SystemAlert

derive instance eqAlertCategory :: Eq AlertCategory

-- | Alert level - Severity level
data AlertLevel
  = Info
  | Warning
  | Critical
  | Success

derive instance eqAlertLevel :: Eq AlertLevel

-- | Alert action - Optional action button
type AlertAction =
  { label :: String
  , onClick :: Effect Unit
  }

-- | Alert data - Complete alert information
type Alert =
  { id :: String
  , category :: AlertCategory
  , level :: AlertLevel
  , title :: String
  , message :: String
  , timestamp :: Number
  , action :: Maybe AlertAction
  , dismissible :: Boolean
  , autoDismissMs :: Maybe Number  -- milliseconds
  }

-- | Component state
type State =
  { alerts :: Array Alert
  , maxVisible :: Int
  , soundEnabled :: Boolean
  , autoDismissTimers :: Map String (Fiber Unit)  -- Track auto-dismiss timers
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
  , maxVisible: 5
  , soundEnabled: false
  , autoDismissTimers: Map.empty
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
  , category: categoryFromType payload.type_
  , level: levelFromString payload.level
  , title: payload.title
  , message: fromMaybe "" payload.message
  , timestamp: 0.0  -- Would parse createdAt from payload.createdAt
  , action: map convertAction payload.actions # Array.head
  , dismissible: payload.dismissible
  , autoDismissMs: map round payload.duration  -- Convert Number to Int milliseconds
  }

-- | Convert notification type to alert category
categoryFromType :: String -> AlertCategory
categoryFromType = case _ of
  "balance" -> BalanceAlert
  "rate_limit" -> RateLimitAlert
  "connection" -> ConnectionAlert
  "proof" -> ProofAlert
  _ -> SystemAlert

-- | Convert notification level string to AlertLevel
levelFromString :: String -> AlertLevel
levelFromString = case _ of
  "success" -> Success
  "info" -> Info
  "warning" -> Warning
  "error" -> Critical
  _ -> Info

-- | Convert notification action to alert action
convertAction :: NotificationAction -> AlertAction
convertAction action =
  { label: action.label
  , onClick: pure unit  -- Would wire to actual action handler
  }

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Initialize alert system
    pure unit
  
  ShowNotification payload -> do
    let alert = notificationToAlert payload
    handleAction (ShowAlert alert)
  
  ShowAlert alert -> do
    -- Add to list
    H.modify_ \s ->
      { s
      | alerts = take s.maxVisible $ cons alert s.alerts
      }
    H.raise (AlertShown alert)
    
    -- Play sound if enabled and critical
    state <- H.get
    when (state.soundEnabled && alert.level == Critical) do
      liftEffect playAlertSound
    
    -- Set up auto-dismiss timer
    case alert.autoDismissMs of
      Just delayMs -> do
        timer <- H.fork $ H.liftAff do
          delay (Milliseconds (Int.toNumber delayMs))
          handleAction (AutoDismiss alert.id)
        -- Store timer for cleanup
        H.modify_ \s ->
          s { autoDismissTimers = Map.insert alert.id timer s.autoDismissTimers }
      Nothing ->
        pure unit
  
  DismissAlert id -> do
    -- Cancel auto-dismiss timer if exists
    state <- H.get
    case Map.lookup id state.autoDismissTimers of
      Just timer -> do
        void $ H.fork $ H.liftAff $ killFiber (error "Dismissed") timer
      Nothing -> pure unit
    
    H.modify_ \s ->
      { s
      | alerts = filter (\a -> a.id /= id) s.alerts
      , autoDismissTimers = Map.delete id s.autoDismissTimers
      }
    H.raise (AlertDismissed id)
  
  AutoDismiss id -> do
    handleAction (DismissAlert id)
  
  ClearAll -> do
    -- Cancel all timers
    state <- H.get
    Map.for_ state.autoDismissTimers \timer ->
      void $ H.fork $ H.liftAff $ killFiber (error "Cleared") timer
    H.modify_ \s ->
      s { alerts = []
      , autoDismissTimers = Map.empty
      }

import Sidepanel.FFI.Sound (playAlertSound)
