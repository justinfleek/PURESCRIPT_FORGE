-- | Diem Tracker Component - Venice Diem Balance Display Widget
-- |
-- | **What:** Specialized widget for displaying Venice Diem balance with countdown timer,
-- |         consumption rate, time-to-depletion projection, and progress bar. Venice-specific
-- |         version of BalanceTracker focused on Diem system.
-- | **Why:** Provides dedicated interface for Venice Diem balance tracking, which has unique
-- |         characteristics (daily reset, staking-based, USD conversion). More focused than
-- |         the general BalanceTracker.
-- | **How:** Displays Diem balance, USD equivalent, effective balance, consumption metrics,
-- |         and progress bar. Updates countdown timer every second via background fiber.
-- |         Triggers alerts when balance thresholds are crossed.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.State.Balance`: Balance state types and alert calculation
-- | - `Sidepanel.Utils.Currency`: Currency formatting
-- | - `Sidepanel.Utils.Time`: Time formatting and countdown
-- |
-- | **Mathematical Foundation:**
-- | - **Alert Level Calculation:** Same as BalanceTracker - calculated based on balance
-- |   thresholds and time-to-depletion.
-- | - **Countdown Timer:** Updates every second via background fiber, recalculates time
-- |   until UTC midnight reset.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.Balance.DiemTracker as DiemTracker
-- |
-- | -- In parent component:
-- | HH.slot _diem unit DiemTracker.component
-- |   { balance: appState.balance, countdown: timeRemaining }
-- |   (case _ of
-- |     DiemTracker.AlertTriggered level -> HandleAlert level
-- |     DiemTracker.SettingsRequested -> NavigateToSettings
-- |     DiemTracker.RefreshRequested -> RefreshBalance)
-- | ```
-- |
-- | Based on spec 51-DIEM-TRACKER-WIDGET.md
module Sidepanel.Components.Balance.DiemTracker where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect, liftEffect)
import Data.Maybe (Maybe(..))
import Data.DateTime (DateTime)
import Sidepanel.State.Balance (BalanceState, AlertLevel(..), calculateAlertLevel)
import Sidepanel.State.Balance as Balance
import Sidepanel.Utils.Currency (formatDiem, formatUSD, formatConsumptionRate, formatTimeToDepletion)
import Sidepanel.Utils.Time (formatTimeRemaining, TimeRemaining, getTimeUntilReset)
import Effect.Aff (Milliseconds(..), delay, forever, forkAff, killFiber, error, Fiber)
import Effect.Class (liftEffect)

-- | Component input
type Input =
  { balance :: BalanceState
  , countdown :: TimeRemaining
  }

-- | Component output
data Output
  = AlertTriggered AlertLevel
  | SettingsRequested
  | RefreshRequested

-- | Internal state
type State =
  { balance :: BalanceState
  , countdown :: TimeRemaining
  , expanded :: Boolean
  , alertLevel :: AlertLevel
  , showTooltip :: Maybe TooltipTarget
  , animationState :: AnimationState
  }

data AnimationState = Idle | Pulsing | Fading

derive instance eqAnimationState :: Eq AnimationState

data TooltipTarget
  = DiemTooltip
  | UsdTooltip
  | EffectiveTooltip
  | RateTooltip
  | ProjectionTooltip
  | ProgressTooltip
  | CountdownTooltip

derive instance eqTooltipTarget :: Eq TooltipTarget

-- | Internal actions
data Action
  = Initialize
  | ReceiveInput Input
  | ToggleExpanded
  | ShowTooltip TooltipTarget
  | HideTooltip
  | OpenSettings
  | RefreshBalance
  | CountdownTick
  | Finalize

-- | Queries from parent
data Query a
  = GetAlertLevel (AlertLevel -> a)
  | ForceRefresh a
  | SetBalance BalanceState a

-- | Component definition
component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , receive = Just <<< ReceiveInput
      , initialize = Just Initialize
      }
  }

initialState :: Input -> State
initialState { balance, countdown } =
  { balance
  , countdown
  , expanded: false
  , alertLevel: calculateAlertLevel balance
  , showTooltip: Nothing
  , animationState: Idle
  , tickerFiber: Nothing
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.classes $ containerClasses state.alertLevel state.animationState
    , HP.attr (H.AttrName "role") "status"
    , HP.attr (H.AttrName "aria-live") "polite"
    , HP.attr (H.AttrName "aria-label") $ 
        "Diem balance: " <> formatDiem (getVeniceDiem state.balance) <>
        ", resets in " <> formatTimeRemaining state.countdown
    ]
    [ renderHeader state
    , renderBalances state
    , renderMetrics state
    , renderProgress state
    , renderTooltip state
    , renderActions state
    ]

containerClasses :: AlertLevel -> AnimationState -> Array H.ClassName
containerClasses level anim =
  [ H.ClassName "diem-tracker" ] <>
  (case level of
    Normal -> []
    Warning -> [ H.ClassName "diem-tracker--warning" ]
    Critical -> [ H.ClassName "diem-tracker--critical" ]
    Depleted -> [ H.ClassName "diem-tracker--depleted" ]) <>
  (case anim of
    Idle -> []
    Pulsing -> [ H.ClassName "diem-tracker--pulsing" ]
    Fading -> [ H.ClassName "diem-tracker--fading" ])

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.div
    [ HP.class_ (H.ClassName "diem-tracker__header") ]
    [ HH.span
        [ HP.class_ (H.ClassName "diem-tracker__title") ]
        [ HH.text "DIEM BALANCE" ]
    , HH.span
        [ HP.class_ (H.ClassName "diem-tracker__countdown")
        , HE.onMouseEnter \_ -> ShowTooltip CountdownTooltip
        , HE.onMouseLeave \_ -> HideTooltip
        ]
        [ HH.text $ "Resets in " <> formatTimeRemaining state.countdown ]
    , renderAlertBadge state.alertLevel
    ]

renderAlertBadge :: forall m. AlertLevel -> H.ComponentHTML Action () m
renderAlertBadge = case _ of
  Normal -> HH.text ""
  Warning -> HH.span
    [ HP.class_ (H.ClassName "alert-badge alert-badge--warning") ]
    [ HH.text "⚠" ]
  Critical -> HH.span
    [ HP.class_ (H.ClassName "alert-badge alert-badge--critical") ]
    [ HH.text "🚨" ]
  Depleted -> HH.span
    [ HP.class_ (H.ClassName "alert-badge alert-badge--depleted") ]
    [ HH.text "DEPLETED" ]

renderBalances :: forall m. State -> H.ComponentHTML Action () m
renderBalances state = case state.balance.venice of
  Just venice ->
    HH.div
      [ HP.class_ (H.ClassName "diem-tracker__balances") ]
      [ HH.div
          [ HP.class_ (H.ClassName "diem-tracker__diem")
          , HE.onMouseEnter \_ -> ShowTooltip DiemTooltip
          , HE.onMouseLeave \_ -> HideTooltip
          ]
          [ HH.span [ HP.class_ (H.ClassName "balance-icon") ] [ HH.text "◉" ]
          , HH.span [ HP.class_ (H.ClassName "balance-value") ]
              [ HH.text $ formatDiem venice.diem ]
          , HH.span [ HP.class_ (H.ClassName "balance-label") ]
              [ HH.text " Diem" ]
          ]
      , HH.div
          [ HP.class_ (H.ClassName "diem-tracker__usd")
          , HE.onMouseEnter \_ -> ShowTooltip UsdTooltip
          , HE.onMouseLeave \_ -> HideTooltip
          ]
          [ HH.text $ "+" <> formatUSD venice.usd <> " USD" ]
      , HH.div
          [ HP.class_ (H.ClassName "diem-tracker__effective")
          , HE.onMouseEnter \_ -> ShowTooltip EffectiveTooltip
          , HE.onMouseLeave \_ -> HideTooltip
          ]
          [ HH.text $ "= " <> formatUSD venice.effective <> " effective" ]
      ]
  Nothing ->
    HH.div
      [ HP.class_ (H.ClassName "diem-tracker__empty") ]
      [ HH.text "No Venice balance available" ]

renderMetrics :: forall m. State -> H.ComponentHTML Action () m
renderMetrics state =
  HH.div
    [ HP.class_ (H.ClassName "diem-tracker__metrics") ]
    [ HH.div
        [ HP.class_ (H.ClassName "metric-card")
        , HE.onMouseEnter \_ -> ShowTooltip RateTooltip
        , HE.onMouseLeave \_ -> HideTooltip
        ]
        [ HH.span [ HP.class_ (H.ClassName "metric-icon") ] [ HH.text "📉" ]
        , HH.span [ HP.class_ (H.ClassName "metric-value") ]
            [ HH.text $ formatConsumptionRate state.balance.consumptionRate ]
        , HH.span [ HP.class_ (H.ClassName "metric-label") ]
            [ HH.text "consumption" ]
        ]
    , HH.div
        [ HP.class_ (H.ClassName "metric-card")
        , HE.onMouseEnter \_ -> ShowTooltip ProjectionTooltip
        , HE.onMouseLeave \_ -> HideTooltip
        ]
        [ HH.span [ HP.class_ (H.ClassName "metric-icon") ] [ HH.text "⏱" ]
        , HH.span [ HP.class_ (H.ClassName "metric-value") ]
            [ HH.text $ formatTimeToDepletionProjection state.balance.timeToDepletion ]
        , HH.span [ HP.class_ (H.ClassName "metric-label") ]
            [ HH.text "at current rate" ]
        ]
    ]

renderProgress :: forall m. State -> H.ComponentHTML Action () m
renderProgress state = case state.balance.venice of
  Just venice ->
    let
      todayUsed = venice.todayUsed
      remaining = venice.diem
      total = todayUsed + remaining
      percentage = if total > 0.0 then (remaining / total) * 100.0 else 0.0
    in
      HH.div
        [ HP.class_ (H.ClassName "diem-tracker__progress")
        , HE.onMouseEnter \_ -> ShowTooltip ProgressTooltip
        , HE.onMouseLeave \_ -> HideTooltip
        ]
        [ HH.span [ HP.class_ (H.ClassName "progress-label-left") ]
            [ HH.text $ "Today: " <> formatDiem todayUsed <> " used" ]
        , HH.div
            [ HP.class_ (H.ClassName "progress-bar") ]
            [ HH.div
                [ HP.class_ (H.ClassName "progress-fill")
                , HP.style $ "width: " <> show percentage <> "%"
                ]
                []
            ]
        , HH.span [ HP.class_ (H.ClassName "progress-label-right") ]
            [ HH.text $ formatDiem remaining <> " remaining" ]
        ]
  Nothing -> HH.text ""

renderTooltip :: forall m. State -> H.ComponentHTML Action () m
renderTooltip state = case state.showTooltip of
  Just target ->
    HH.div
      [ HP.class_ (H.ClassName "tooltip") ]
      [ HH.text $ getTooltipContent target state.balance ]
  Nothing -> HH.text ""

renderActions :: forall m. State -> H.ComponentHTML Action () m
renderActions state =
  HH.div
    [ HP.class_ (H.ClassName "diem-tracker__actions") ]
    [ HH.button
        [ HP.classes [ H.ClassName "btn-icon" ]
        , HP.title "Refresh balance"
        , HE.onClick \_ -> RefreshBalance
        ]
        [ HH.text "↻" ]
    , HH.button
        [ HP.classes [ H.ClassName "btn-icon" ]
        , HP.title "Settings"
        , HE.onClick \_ -> OpenSettings
        ]
        [ HH.text "⚙" ]
    ]

getTooltipContent :: TooltipTarget -> BalanceState -> String
getTooltipContent target balance = case target of
  DiemTooltip ->
    case balance.venice of
      Just venice -> "Venice Diem Balance\n\nEarned from staking VVV tokens.\nResets daily at midnight UTC.\n1 Diem = $1 API credit.\n\nCurrent: " <> formatDiem venice.diem
      Nothing -> "Venice Diem Balance\n\nNo Venice balance data available."
  UsdTooltip ->
    case balance.venice of
      Just venice -> "USD Balance\n\nDeposited funds that don't reset.\nUsed after Diem is depleted.\nCurrent: " <> formatUSD venice.usd
      Nothing -> "USD Balance\n\nNo Venice balance data available."
  EffectiveTooltip ->
    case balance.venice of
      Just venice -> "Effective Balance\n\nTotal available API credit.\nDiem + USD combined.\nCurrent: " <> formatUSD venice.effective
      Nothing -> "Effective Balance\n\nNo Venice balance data available."
  RateTooltip ->
    "Consumption Rate\n\nAverage tokens spent per hour\nbased on last 60 minutes.\n\nCurrent: " <> formatConsumptionRate balance.consumptionRate
  ProjectionTooltip ->
    case balance.timeToDepletion of
      Nothing -> "Time to Depletion\n\nNot depleting (rate is 0)"
      Just hours -> "Time to Depletion\n\nEstimated time until Diem\nreaches zero at current rate.\n\nProjected: " <> formatTimeToDepletion hours
  ProgressTooltip ->
    case balance.venice of
      Just venice -> "Today's Usage\n\nUsed: " <> formatDiem venice.todayUsed <> "\nRemaining: " <> formatDiem venice.diem
      Nothing -> "Today's Usage\n\nNo Venice balance data available."
  CountdownTooltip ->
    "Reset Countdown\n\nVenice Diem balance resets to daily\nallocation at midnight UTC."

formatTimeToDepletionProjection :: Maybe Number -> String
formatTimeToDepletionProjection = case _ of
  Nothing -> "∞"
  Just hours -> formatTimeToDepletion hours

-- Alert level calculation imported from Balance module

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Start countdown ticker (updates every second)
    tickerFiber <- H.liftAff $ forkAff $ forever do
      delay (Milliseconds 1000.0)
      H.raise CountdownTick
    -- Store ticker fiber in state for cleanup
    H.modify_ _ { tickerFiber = Just tickerFiber }
    pure unit

  ReceiveInput { balance, countdown } -> do
    let newAlertLevel = calculateAlertLevel balance
    oldState <- H.get
    
    -- Check if alert level changed
    when (newAlertLevel /= oldState.alertLevel) do
      H.raise $ AlertTriggered newAlertLevel
      -- Update animation state
      H.modify_ _ { animationState = case newAlertLevel of
          Critical -> Pulsing
          Depleted -> Pulsing
          Warning -> Fading
          Normal -> Idle
        }
    
    H.modify_ _ { balance = balance, countdown = countdown, alertLevel = newAlertLevel }

  ToggleExpanded ->
    H.modify_ \s -> s { expanded = not s.expanded }

  ShowTooltip target ->
    H.modify_ _ { showTooltip = Just target }

  HideTooltip ->
    H.modify_ _ { showTooltip = Nothing }

  OpenSettings ->
    H.raise SettingsRequested

  RefreshBalance ->
    H.raise RefreshRequested

  CountdownTick -> do
    -- Recalculate countdown from current time
    newCountdown <- liftEffect getTimeUntilReset
    H.modify_ _ { countdown = newCountdown }
  
  Finalize -> do
    -- Cleanup: kill ticker fiber if it exists
    tickerFiber <- H.gets _.tickerFiber
    case tickerFiber of
      Just fiber -> H.liftAff $ killFiber (error "Component finalizing") fiber
      Nothing -> pure unit

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  GetAlertLevel k -> do
    state <- H.get
    pure $ Just (k state.alertLevel)

  ForceRefresh k -> do
    H.raise RefreshRequested
    pure (Just k)

  SetBalance balance k -> do
    countdown <- H.gets _.countdown
    H.modify_ _ { balance = balance, alertLevel = calculateAlertLevel balance }
    pure (Just k)
