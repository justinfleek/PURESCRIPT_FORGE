-- | Balance Tracker Component - Comprehensive Token Balance Display
-- |
-- | **What:** Displays token balance information across all providers, with special support
-- |         for Venice Diem system. Shows balances, consumption rates, cost metrics, progress
-- |         bars, and countdown timers. Supports multiple display modes (All Providers, Venice
-- |         Only, Provider-specific).
-- | **Why:** Provides users with real-time visibility into their token usage, costs, and
-- |         remaining balance. Critical for budget management and usage tracking.
-- | **How:** Renders balance widgets with provider selection, displays Venice Diem with
-- |         countdown timer, shows consumption rates and projections, and provides alert
-- |         indicators. Updates alert level based on balance thresholds.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.State.Balance`: Balance state types and alert calculation
-- | - `Sidepanel.Utils.Currency`: Currency formatting
-- | - `Sidepanel.Utils.Time`: Time formatting and countdown
-- |
-- | **Mathematical Foundation:**
-- | - **Alert Level Calculation:** Alert level is calculated based on balance thresholds
-- |   (warningPercent, criticalPercent) and time-to-depletion projections.
-- | - **Consumption Rate:** Calculated as average tokens per hour based on recent activity.
-- | - **Time to Depletion:** Projected time until balance reaches zero at current consumption
-- |   rate. Formula: `hours = balance / consumptionRate`.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.Balance.BalanceTracker as BalanceTracker
-- |
-- | -- In parent component:
-- | HH.slot _balance unit BalanceTracker.component
-- |   { balance: appState.balance
-- |   , countdown: timeRemaining
-- |   , selectedProvider: Just "venice"
-- |   }
-- |   (case _ of
-- |     BalanceTracker.AlertTriggered level -> HandleAlert level
-- |     BalanceTracker.SettingsRequested -> NavigateToSettings
-- |     BalanceTracker.RefreshRequested -> RefreshBalance)
-- | ```
-- |
-- | Based on spec 51-DIEM-TRACKER-WIDGET.md
module Sidepanel.Components.Balance.BalanceTracker where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)
import Effect.Class (class MonadEffect, liftEffect)
import Data.Maybe (Maybe(..))
import Data.DateTime (DateTime)
import Data.Map as Map
import Data.String as String
import Data.Int (toNumber)
import Sidepanel.State.Balance (BalanceState, VeniceBalance, FlkBalance, TokenUsage, AlertLevel(..), calculateAlertLevel)
import Sidepanel.Utils.Currency (formatDiem, formatFLK, formatUSD, formatConsumptionRate, formatTimeToDepletion)
import Sidepanel.Utils.Time (formatTimeRemaining, TimeRemaining, getTimeUntilReset)

-- | Display mode
data DisplayMode
  = AllProviders      -- Show aggregated across all providers
  | Provider String   -- Show specific provider
  | VeniceOnly        -- Show Venice Diem system
  | FlkOnly           -- Show Fleek Token (FLK) balance

derive instance eqDisplayMode :: Eq DisplayMode

-- | Component input
type Input =
  { balance :: BalanceState
  , countdown :: TimeRemaining
  , selectedProvider :: Maybe String
  }

-- | Component output
data Output
  = AlertTriggered AlertLevel
  | SettingsRequested
  | RefreshRequested
  = ProviderSelected String

-- | Internal state
type State =
  { balance :: BalanceState
  , countdown :: TimeRemaining
  , displayMode :: DisplayMode
  , expanded :: Boolean
  , alertLevel :: AlertLevel
  , showTooltip :: Maybe TooltipTarget
  , animationState :: AnimationState
  }

data AnimationState = Idle | Pulsing | Fading

derive instance eqAnimationState :: Eq AnimationState

data TooltipTarget
  = BalanceTooltip
  | TokenTooltip
  | CostTooltip
  | RateTooltip
  | ProjectionTooltip
  | ProgressTooltip
  | CountdownTooltip
  | ProviderTooltip

derive instance eqTooltipTarget :: Eq TooltipTarget

-- | Internal actions
data Action
  = Initialize
  | ReceiveInput Input
  | SetDisplayMode DisplayMode
  | ToggleExpanded
  | ShowTooltip TooltipTarget
  | HideTooltip
  | OpenSettings
  | RefreshBalance
  | CountdownTick

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
initialState { balance, countdown, selectedProvider } =
  { balance
  , countdown
  , displayMode: case selectedProvider of
      Just "venice" -> VeniceOnly
      Just pid -> Provider pid
      Nothing -> AllProviders
  , expanded: false
  , alertLevel: calculateAlertLevel balance
  , showTooltip: Nothing
  , animationState: Idle
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.classes $ containerClasses state.alertLevel state.animationState
    , HP.attr (H.AttrName "role") "status"
    , HP.attr (H.AttrName "aria-live") "polite"
    , HP.attr (H.AttrName "aria-label") $ getAriaLabel state
    ]
    [ renderHeader state
    , renderProviderSelector state
    , renderBalances state
    , renderTokenMetrics state
    , renderCostMetrics state
    , renderProgress state
    , renderTooltip state
    , renderActions state
    ]

getAriaLabel :: State -> String
getAriaLabel state = case state.displayMode of
  VeniceOnly -> 
    "Venice Diem balance: " <> formatDiem (getVeniceDiem state.balance) <>
    ", resets in " <> formatTimeRemaining state.countdown
  FlkOnly ->
    case getFlkBalance state.balance of
      Just flk -> "FLK balance: " <> formatFLK flk.flk
      Nothing -> "No FLK balance available"
  AllProviders ->
    "Total tokens: " <> show state.balance.totalTokens.totalTokens <>
    ", total cost: " <> formatUSD state.balance.totalCost
  Provider pid ->
    "Provider " <> pid <> " balance"

getVeniceDiem :: BalanceState -> Number
getVeniceDiem balance = case balance.venice of
  Just venice -> venice.diem
  Nothing -> 0.0

containerClasses :: AlertLevel -> AnimationState -> Array H.ClassName
containerClasses level anim =
  [ H.ClassName "balance-tracker" ] <>
  (case level of
    Normal -> []
    Warning -> [ H.ClassName "balance-tracker--warning" ]
    Critical -> [ H.ClassName "balance-tracker--critical" ]
    Depleted -> [ H.ClassName "balance-tracker--depleted" ]) <>
  (case anim of
    Idle -> []
    Pulsing -> [ H.ClassName "balance-tracker--pulsing" ]
    Fading -> [ H.ClassName "balance-tracker--fading" ])

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.div
    [ HP.class_ (H.ClassName "balance-tracker__header") ]
    [ HH.span
        [ HP.class_ (H.ClassName "balance-tracker__title") ]
        [ HH.text $ getTitle state.displayMode ]
    , case state.displayMode of
        VeniceOnly ->
          HH.span
            [ HP.class_ (H.ClassName "balance-tracker__countdown")
            , HE.onMouseEnter \_ -> ShowTooltip CountdownTooltip
            , HE.onMouseLeave \_ -> HideTooltip
            ]
            [ HH.text $ "Resets in " <> formatTimeRemaining state.countdown ]
        FlkOnly -> HH.text ""  -- FLK doesn't have countdown
        _ -> HH.text ""
    , renderAlertBadge state
    ]

getTitle :: DisplayMode -> String
getTitle = case _ of
  AllProviders -> "TOKEN BALANCE"
  VeniceOnly -> "DIEM BALANCE"
  FlkOnly -> "FLK BALANCE"
  Provider pid -> "BALANCE: " <> toUpper pid

toUpper :: String -> String
toUpper s = String.toUpper s

renderProviderSelector :: forall m. State -> H.ComponentHTML Action () m
renderProviderSelector state =
  HH.div
    [ HP.class_ (H.ClassName "balance-tracker__provider-selector") ]
    [ HH.button
        [ HP.classes $ providerButtonClasses (state.displayMode == AllProviders)
        , HE.onClick \_ -> SetDisplayMode AllProviders
        ]
        [ HH.text "All" ]
    , HH.button
        [ HP.classes $ providerButtonClasses (state.displayMode == VeniceOnly)
        , HE.onClick \_ -> SetDisplayMode VeniceOnly
        ]
        [ HH.text "Venice" ]
    , HH.text " | "
    , HH.text "Other providers..."  -- Would list all providers
    ]

providerButtonClasses :: Boolean -> Array H.ClassName
providerButtonClasses isActive =
  [ H.ClassName "provider-btn" ] <>
  if isActive then [ H.ClassName "provider-btn--active" ] else []

renderBalances :: forall m. State -> H.ComponentHTML Action () m
renderBalances state = case state.displayMode of
  VeniceOnly -> renderVeniceBalances state
  FlkOnly -> renderFlkBalances state
  AllProviders -> renderAggregatedBalances state
  Provider pid -> renderProviderBalances state pid

renderVeniceBalances :: forall m. State -> H.ComponentHTML Action () m
renderVeniceBalances state = case state.balance.venice of
  Just venice ->
    HH.div
      [ HP.class_ (H.ClassName "balance-tracker__balances") ]
      [ HH.div
          [ HP.class_ (H.ClassName "balance-tracker__diem")
          , HE.onMouseEnter \_ -> ShowTooltip BalanceTooltip
          , HE.onMouseLeave \_ -> HideTooltip
          ]
          [ HH.span [ HP.class_ (H.ClassName "balance-icon") ] [ HH.text "◉" ]
          , HH.span [ HP.class_ (H.ClassName "balance-value") ]
              [ HH.text $ formatDiem venice.diem ]
          , HH.span [ HP.class_ (H.ClassName "balance-label") ]
              [ HH.text " Diem" ]
          ]
      , HH.div
          [ HP.class_ (H.ClassName "balance-tracker__usd") ]
          [ HH.text $ "+" <> formatUSD venice.usd <> " USD" ]
      , HH.div
          [ HP.class_ (H.ClassName "balance-tracker__effective") ]
          [ HH.text $ "= " <> formatUSD venice.effective <> " effective" ]
      ]
  Nothing ->
    HH.div
      [ HP.class_ (H.ClassName "balance-tracker__empty") ]
      [ HH.text "No Venice balance data" ]

-- | Render FLK balances - Display FLK balance information
-- |
-- | **Purpose:** Renders FLK balance display with balance value, effective balance,
-- |             and today's usage. Similar to Venice balance display but without
-- |             countdown (FLK doesn't reset daily).
-- | **Parameters:**
-- | - `state`: Current component state
-- | **Returns:** Halogen HTML for FLK balance display
-- | **Side Effects:** None (pure rendering)
renderFlkBalances :: forall m. State -> H.ComponentHTML Action () m
renderFlkBalances state = case getFlkBalance state.balance of
  Just flk ->
    HH.div
      [ HP.class_ (H.ClassName "balance-tracker__balances") ]
      [ HH.div
          [ HP.class_ (H.ClassName "balance-tracker__flk")
          , HE.onMouseEnter \_ -> ShowTooltip BalanceTooltip
          , HE.onMouseLeave \_ -> HideTooltip
          ]
          [ HH.span [ HP.class_ (H.ClassName "balance-icon") ] [ HH.text "⚡" ]
          , HH.span [ HP.class_ (H.ClassName "balance-value") ]
              [ HH.text $ formatFLK flk.flk ]
          , HH.span [ HP.class_ (H.ClassName "balance-label") ]
              [ HH.text " FLK" ]
          ]
      , HH.div
          [ HP.class_ (H.ClassName "balance-tracker__effective") ]
          [ HH.text $ "= " <> formatFLK flk.effective <> " effective" ]
      , HH.div
          [ HP.class_ (H.ClassName "balance-tracker__today-used") ]
          [ HH.text $ "Today: " <> formatFLK flk.todayUsed <> " used" ]
      ]
  Nothing ->
    HH.div
      [ HP.class_ (H.ClassName "balance-tracker__empty") ]
      [ HH.text "No FLK balance data" ]

renderAggregatedBalances :: forall m. State -> H.ComponentHTML Action () m
renderAggregatedBalances state =
  HH.div
    [ HP.class_ (H.ClassName "balance-tracker__balances") ]
    [ HH.div
        [ HP.class_ (H.ClassName "balance-tracker__tokens")
        , HE.onMouseEnter \_ -> ShowTooltip TokenTooltip
        , HE.onMouseLeave \_ -> HideTooltip
        ]
        [ HH.span [ HP.class_ (H.ClassName "balance-icon") ] [ HH.text "🔢" ]
        , HH.span [ HP.class_ (H.ClassName "balance-value") ]
            [ HH.text $ formatNumber state.balance.totalTokens.totalTokens ]
        , HH.span [ HP.class_ (H.ClassName "balance-label") ]
            [ HH.text " tokens" ]
        ]
    , HH.div
        [ HP.class_ (H.ClassName "balance-tracker__cost")
        , HE.onMouseEnter \_ -> ShowTooltip CostTooltip
        , HE.onMouseLeave \_ -> HideTooltip
        ]
        [ HH.text $ formatUSD state.balance.totalCost <> " total" ]
    , HH.div
        [ HP.class_ (H.ClassName "balance-tracker__today-cost") ]
        [ HH.text $ formatUSD state.balance.totalCostToday <> " today" ]
    ]

renderProviderBalances :: forall m. State -> String -> H.ComponentHTML Action () m
renderProviderBalances state providerId =
  case Map.lookup providerId state.balance.providerBalances of
    Just providerBalance ->
      HH.div
        [ HP.class_ (H.ClassName "balance-tracker__balances") ]
        [ HH.div
            [ HP.class_ (H.ClassName "balance-tracker__tokens") ]
            [ HH.text $ formatNumber providerBalance.tokenUsage.totalTokens <> " tokens" ]
        , HH.div
            [ HP.class_ (H.ClassName "balance-tracker__cost") ]
            [ HH.text $ formatUSD providerBalance.cost ]
        ]
    Nothing ->
      HH.div
        [ HP.class_ (H.ClassName "balance-tracker__empty") ]
        [ HH.text $ "No data for provider: " <> providerId ]

renderTokenMetrics :: forall m. State -> H.ComponentHTML Action () m
renderTokenMetrics state =
  HH.div
    [ HP.class_ (H.ClassName "balance-tracker__metrics") ]
    [ HH.div
        [ HP.class_ (H.ClassName "metric-card")
        , HE.onMouseEnter \_ -> ShowTooltip RateTooltip
        , HE.onMouseLeave \_ -> HideTooltip
        ]
        [ HH.span [ HP.class_ (H.ClassName "metric-icon") ] [ HH.text "📉" ]
        , HH.span [ HP.class_ (H.ClassName "metric-value") ]
            [ HH.text $ formatConsumptionRate state.balance.consumptionRate ]
        , HH.span [ HP.class_ (H.ClassName "metric-label") ]
            [ HH.text "tokens/hr" ]
        ]
    , case state.displayMode of
        VeniceOnly ->
          HH.div
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
        FlkOnly ->
          HH.div
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
        _ ->
          HH.div
            [ HP.class_ (H.ClassName "metric-card") ]
            [ HH.span [ HP.class_ (H.ClassName "metric-icon") ] [ HH.text "💰" ]
            , HH.span [ HP.class_ (H.ClassName "metric-value") ]
                [ HH.text $ formatUSD state.balance.costRate ]
            , HH.span [ HP.class_ (H.ClassName "metric-label") ]
                [ HH.text "cost/hr" ]
            ]
    ]

renderCostMetrics :: forall m. State -> H.ComponentHTML Action () m
renderCostMetrics state =
  HH.div
    [ HP.class_ (H.ClassName "balance-tracker__cost-breakdown") ]
    [ HH.div
        [ HP.class_ (H.ClassName "cost-item") ]
        [ HH.span [ HP.class_ (H.ClassName "cost-label") ] [ HH.text "Today:" ]
        , HH.span [ HP.class_ (H.ClassName "cost-value") ]
            [ HH.text $ formatUSD state.balance.todayCost ]
        ]
    , HH.div
        [ HP.class_ (H.ClassName "cost-item") ]
        [ HH.span [ HP.class_ (H.ClassName "cost-label") ] [ HH.text "Total:" ]
        , HH.span [ HP.class_ (H.ClassName "cost-value") ]
            [ HH.text $ formatUSD state.balance.totalCost ]
        ]
    ]

renderProgress :: forall m. State -> H.ComponentHTML Action () m
renderProgress state = case state.displayMode of
  VeniceOnly -> renderVeniceProgress state
  FlkOnly -> renderFlkProgress state
  _ -> renderTokenProgress state

renderVeniceProgress :: forall m. State -> H.ComponentHTML Action () m
renderVeniceProgress state = case state.balance.venice of
  Just venice ->
    let
      todayUsed = venice.todayUsed
      remaining = venice.diem
      total = todayUsed + remaining
      percentage = if total > 0.0 then (remaining / total) * 100.0 else 0.0
    in
      HH.div
        [ HP.class_ (H.ClassName "balance-tracker__progress")
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

-- | Render FLK progress - Display FLK usage progress bar
-- |
-- | **Purpose:** Renders progress bar showing FLK balance and today's usage.
-- |             Similar to Venice progress but without reset countdown.
-- | **Parameters:**
-- | - `state`: Current component state
-- | **Returns:** Halogen HTML for FLK progress display
-- | **Side Effects:** None (pure rendering)
renderFlkProgress :: forall m. State -> H.ComponentHTML Action () m
renderFlkProgress state = case getFlkBalance state.balance of
  Just flk ->
    let
      todayUsed = flk.todayUsed
      remaining = flk.flk
      total = todayUsed + remaining
      percentage = if total > 0.0 then (remaining / total) * 100.0 else 0.0
    in
      HH.div
        [ HP.class_ (H.ClassName "balance-tracker__progress")
        , HE.onMouseEnter \_ -> ShowTooltip ProgressTooltip
        , HE.onMouseLeave \_ -> HideTooltip
        ]
        [ HH.span [ HP.class_ (H.ClassName "progress-label-left") ]
            [ HH.text $ "Today: " <> formatFLK todayUsed <> " used" ]
        , HH.div
            [ HP.class_ (H.ClassName "progress-bar") ]
            [ HH.div
                [ HP.class_ (H.ClassName "progress-fill")
                , HP.style $ "width: " <> show percentage <> "%"
                ]
                []
            ]
        , HH.span [ HP.class_ (H.ClassName "progress-label-right") ]
            [ HH.text $ formatFLK remaining <> " remaining" ]
        ]
  Nothing -> HH.text ""

renderTokenProgress :: forall m. State -> H.ComponentHTML Action () m
renderTokenProgress state =
  let
    todayUsed = state.balance.todayUsed.totalTokens
    -- Calculate percentage based on context budget total (1M tokens default)
    -- If daily limit is configured, would use that instead
    dailyLimit = 1000000  -- Default context window (1M tokens)
    percentage = if dailyLimit > 0 then (toNumber todayUsed / toNumber dailyLimit) * 100.0 else 0.0
  in
    HH.div
      [ HP.class_ (H.ClassName "balance-tracker__progress") ]
      [ HH.span [ HP.class_ (H.ClassName "progress-label-left") ]
          [ HH.text $ "Today: " <> formatNumber todayUsed <> " tokens" ]
      , HH.div
          [ HP.class_ (H.ClassName "progress-bar") ]
          [ HH.div
              [ HP.class_ (H.ClassName "progress-fill")
              , HP.style $ "width: " <> show percentage <> "%"
              ]
              []
          ]
      , HH.span [ HP.class_ (H.ClassName "progress-label-right") ]
          [ HH.text $ formatUSD state.balance.todayCost <> " cost" ]
      ]

renderTooltip :: forall m. State -> H.ComponentHTML Action () m
renderTooltip state = case state.showTooltip of
  Just target ->
    HH.div
      [ HP.class_ (H.ClassName "tooltip") ]
      [ HH.text $ getTooltipContent target state.balance state.displayMode ]
  Nothing -> HH.text ""

getTooltipContent :: TooltipTarget -> BalanceState -> DisplayMode -> String
getTooltipContent target balance displayMode = case target of
  BalanceTooltip ->
    case displayMode of
      VeniceOnly -> "Venice Diem Balance\n\nEarned from staking VVV tokens.\nResets daily at midnight UTC.\n1 Diem = $1 API credit."
      FlkOnly -> 
        case balance.flk of
          Just flk -> "FLK Balance\n\nFleek Token (FLK) balance.\n1 FLK = 1 API credit equivalent.\nDoes not reset daily.\n\nCurrent: " <> formatFLK flk.flk
          Nothing -> "FLK Balance\n\nNo FLK balance data available."
      _ -> "Balance\n\nCurrent available balance for selected provider."
  TokenTooltip ->
    "Token Usage\n\nTotal tokens consumed across all providers.\nPrompt + Completion tokens."
  CostTooltip ->
    "Total Cost\n\nCumulative cost across all providers.\nTracked in USD."
  RateTooltip ->
    "Consumption Rate\n\nAverage tokens spent per hour\nbased on recent activity."
  ProjectionTooltip ->
    case balance.timeToDepletion of
      Nothing -> "Time to Depletion\n\nNot depleting (rate is 0)"
      Just hours -> 
        case displayMode of
          FlkOnly -> "Time to Depletion\n\nEstimated time until FLK\nreaches zero at current rate.\n\nProjected: " <> formatTimeToDepletion hours
          _ -> "Time to Depletion\n\nEstimated time until Diem\nreaches zero at current rate.\n\nProjected: " <> formatTimeToDepletion hours
  ProgressTooltip ->
    case displayMode of
      VeniceOnly -> "Today's Usage\n\nDiem consumed today.\nResets at midnight UTC."
      FlkOnly -> 
        case balance.flk of
          Just flk -> "Today's Usage\n\nFLK consumed today: " <> formatFLK flk.todayUsed <> "\nRemaining: " <> formatFLK flk.flk
          Nothing -> "Today's Usage\n\nNo FLK balance data available."
      _ -> "Today's Usage\n\nTokens and cost consumed today."
  CountdownTooltip ->
    "Reset Countdown\n\nVenice Diem balance resets to daily\nallocation at midnight UTC.\n(FLK does not reset)"
  ProviderTooltip ->
    "Provider Selection\n\nSwitch between providers to view\nprovider-specific balances and usage.\n\nAvailable: All, Venice, FLK"

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

renderActions :: forall m. State -> H.ComponentHTML Action () m
renderActions state =
  HH.div
    [ HP.class_ (H.ClassName "balance-tracker__actions") ]
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

formatTimeToDepletionProjection :: Maybe Number -> String
formatTimeToDepletionProjection = case _ of
  Nothing -> "∞"
  Just hours -> formatTimeToDepletion hours

formatNumber :: Int -> String
formatNumber n = show n

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  ReceiveInput { balance, countdown, selectedProvider } -> do
    let newAlertLevel = calculateAlertLevel balance
    oldState <- H.get
    
    when (newAlertLevel /= oldState.alertLevel) do
      H.raise $ AlertTriggered newAlertLevel
      H.modify_ _ { animationState = case newAlertLevel of
          Critical -> Pulsing
          Depleted -> Pulsing
          Warning -> Fading
          Normal -> Idle
        }
    
    displayMode <- case selectedProvider of
      Just "venice" -> pure VeniceOnly
      Just "flk" -> pure FlkOnly
      Just pid -> pure (Provider pid)
      Nothing -> pure AllProviders
    
    H.modify_ _ { balance = balance, countdown = countdown, alertLevel = newAlertLevel, displayMode = displayMode }

  SetDisplayMode mode -> do
    H.modify_ _ { displayMode = mode }
    case mode of
      Provider pid -> H.raise (ProviderSelected pid)
      _ -> pure unit

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

  CountdownTick -> pure unit

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
    displayMode <- H.gets _.displayMode
    H.modify_ _ { balance = balance, alertLevel = calculateAlertLevel balance }
    pure (Just k)
