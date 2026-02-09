-- | Countdown Timer Component - Venice Diem Reset Countdown
-- |
-- | **What:** Displays a countdown timer showing time remaining until Venice Diem balance
-- |         resets at UTC midnight. Updates every second and shows urgency levels (Normal,
-- |         Warning, Critical) based on time remaining.
-- | **Why:** Provides clear visual feedback about when Diem balance will reset, helping
-- |         users plan their usage. Urgency levels alert users when reset is approaching.
-- | **How:** Calculates time until UTC midnight, updates every second via ticker emitter,
-- |         formats time display based on remaining duration, and shows tooltip with
-- |         detailed information on hover.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.Utils.Time`: Time calculation and formatting utilities
-- |
-- | **Mathematical Foundation:**
-- | - **Urgency Calculation:** Critical (< 30 minutes), Warning (< 2 hours), Normal (≥ 2 hours).
-- | - **Time Formatting:** Shows seconds only in final minute, minutes+seconds when < 1 hour,
-- |   hours+minutes+seconds when ≥ 1 hour.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.Balance.CountdownTimer as CountdownTimer
-- |
-- | -- In parent component:
-- | HH.slot _countdown unit CountdownTimer.component
-- |   { timezone: Just "America/New_York" }
-- |   (const HandleAppAction)
-- | ```
-- |
-- | Spec 52: Reset Countdown Component
module Sidepanel.Components.Balance.CountdownTimer where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff, liftAff)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Aff (Milliseconds(..), delay, forever, forkAff, killFiber, error)
import Data.Maybe (Maybe(..))
import Data.Array as Array
import Sidepanel.Utils.Time (TimeRemaining, getTimeUntilReset, formatTimeRemaining, formatTimeRemainingCompact)

-- | Urgency levels for styling
data UrgencyLevel = Normal | Warning | Critical

derive instance eqUrgencyLevel :: Eq UrgencyLevel

-- | Component input
type Input = 
  { timezone :: Maybe String  -- For tooltip display
  }

-- | Component state
type State =
  { timeRemaining :: TimeRemaining
  , urgencyLevel :: UrgencyLevel
  , showTooltip :: Boolean
  }

-- | Component actions
data Action
  = Initialize
  | Tick
  | ToggleTooltip Boolean

-- | No output (purely display component)
type Output = Void

-- | Component definition
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

initialState :: Input -> State
initialState _ =
  { timeRemaining: { hours: 0, minutes: 0, seconds: 0, totalMs: 0.0 }
  , urgencyLevel: Normal
  , showTooltip: false
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.classes $ containerClasses state.urgencyLevel
    , HP.attr (H.AttrName "role") "timer"
    , HP.attr (H.AttrName "aria-live") "polite"
    , HP.attr (H.AttrName "aria-label") $ "Diem resets in " <> formatAccessible state.timeRemaining
    , HE.onMouseEnter \_ -> ToggleTooltip true
    , HE.onMouseLeave \_ -> ToggleTooltip false
    ]
    [ -- Urgency icon (warning/critical only)
      case state.urgencyLevel of
        Normal -> HH.text ""
        _ -> HH.span 
            [ HP.class_ (H.ClassName "countdown__icon") ] 
            [ HH.text "⚠" ]
    
    -- Label
    , HH.span 
        [ HP.class_ (H.ClassName "countdown__label") ]
        [ HH.text "Resets in " ]
    
    -- Time display
    , HH.span 
        [ HP.class_ (H.ClassName "countdown__time") ]
        [ HH.text $ formatTime state.timeRemaining ]
    
    -- Tooltip
    , if state.showTooltip then renderTooltip state else HH.text ""
    ]

renderTooltip :: forall m. State -> H.ComponentHTML Action () m
renderTooltip state =
  HH.div
    [ HP.class_ (H.ClassName "countdown__tooltip") ]
    [ HH.div_ [ HH.text "Midnight UTC (00:00:00)" ]
    , HH.div_ [ HH.text $ "Your time: " <> getLocalResetTime ]
    , HH.div_ [ HH.text $ formatVerbose state.timeRemaining ]
    ]

containerClasses :: UrgencyLevel -> Array H.ClassName
containerClasses level =
  [ H.ClassName "countdown" ] <> case level of
    Normal -> []
    Warning -> [ H.ClassName "countdown--warning" ]
    Critical -> [ H.ClassName "countdown--critical" ]

-- | Handle actions
handleAction :: forall m. MonadAff m 
             => Action 
             -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Calculate initial time
    time <- liftEffect getTimeUntilReset
    let urgency = calculateUrgency time
    H.modify_ _ { timeRemaining = time, urgencyLevel = urgency }
    
    -- Start ticker subscription
    void $ H.subscribe tickerEmitter

  Tick -> do
    time <- liftEffect getTimeUntilReset
    let urgency = calculateUrgency time
    H.modify_ _ { timeRemaining = time, urgencyLevel = urgency }
    
    -- Check if we just crossed midnight
    when (time.totalMs <= 0.0) do
      -- Reset already occurred, recalculate for tomorrow
      liftAff $ delay (Milliseconds 100.0)
      newTime <- liftEffect getTimeUntilReset
      H.modify_ _ { timeRemaining = newTime }

  ToggleTooltip show ->
    H.modify_ _ { showTooltip = show }

-- | Ticker that fires every second
tickerEmitter :: forall m. MonadAff m => H.Emitter m Action
tickerEmitter = H.Emitter \emit -> do
  fiber <- forkAff $ forever do
    delay (Milliseconds 1000.0)
    liftEffect $ emit Tick
  pure $ killFiber (error "unsubscribed") fiber

-- | Calculate urgency level based on time remaining
calculateUrgency :: TimeRemaining -> UrgencyLevel
calculateUrgency { totalMs } =
  let hours = totalMs / 3600000.0
  in
    if hours < 0.5 then Critical  -- < 30 minutes
    else if hours < 2.0 then Warning  -- < 2 hours
    else Normal

-- | Format time for display
formatTime :: TimeRemaining -> String
formatTime { hours, minutes, seconds, totalMs } =
  let totalSeconds = floor (totalMs / 1000.0)
  in
    if totalSeconds < 60 then
      -- Final minute: show seconds only
      "0:" <> pad seconds
    else if hours > 0 then
      -- Show hours, minutes, seconds
      show hours <> "h " <> pad minutes <> "m " <> pad seconds <> "s"
    else
      -- Show minutes and seconds
      pad minutes <> "m " <> pad seconds <> "s"
  where
    pad n = if n < 10 then "0" <> show n else show n

-- | Format time for accessibility (screen readers)
formatAccessible :: TimeRemaining -> String
formatAccessible { hours, minutes, seconds } =
  let parts = Array.catMaybes
        [ if hours > 0 then Just (show hours <> " hour" <> if hours == 1 then "" else "s") else Nothing
        , if minutes > 0 then Just (show minutes <> " minute" <> if minutes == 1 then "" else "s") else Nothing
        , if seconds > 0 then Just (show seconds <> " second" <> if seconds == 1 then "" else "s") else Nothing
        ]
  in
    case parts of
      [] -> "less than a second"
      [one] -> one
      [one, two] -> one <> " and " <> two
      [one, two, three] -> one <> ", " <> two <> ", and " <> three
      _ -> formatTimeRemaining { hours, minutes, seconds, totalMs: 0.0 }

-- | Format verbose time for tooltip
formatVerbose :: TimeRemaining -> String
formatVerbose { hours, minutes, seconds } =
  show hours <> " hours, " <> show minutes <> " minutes, " <> show seconds <> " seconds"

-- | Get local reset time (UTC midnight displayed in local timezone)
-- | For now, returns UTC midnight time - in production would convert to user's timezone
getLocalResetTime :: String
getLocalResetTime = "00:00:00 UTC"
