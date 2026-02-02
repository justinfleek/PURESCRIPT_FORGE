-- | BalanceTracker Render Functions
-- |
-- | Rendering functions for the balance tracker component.
-- |
-- | Coeffect Equation:
-- |   Render : State -> H.ComponentHTML Action () m
-- |   with display modes: Venice | FLK | All | Provider
-- |
-- | Module Coverage: Header, balances, metrics, progress, tooltips
module Sidepanel.Components.Balance.BalanceTracker.Render
  ( render
  , renderHeader
  , renderProviderSelector
  , renderBalances
  , renderTokenMetrics
  , renderCostMetrics
  , renderProgress
  , renderTooltip
  , renderActions
  , renderAlertBadge
  ) where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Data.Maybe (Maybe(..))
import Data.Map as Map
import Data.String as String
import Data.Int (toNumber)
import Sidepanel.State.Balance (BalanceState, AlertLevel(..))
import Sidepanel.Utils.Currency (formatDiem, formatFLK, formatUSD, formatConsumptionRate, formatTimeToDepletion)
import Sidepanel.Utils.Time (formatTimeRemaining)
import Sidepanel.Components.Balance.BalanceTracker.Types
  ( State
  , Action(..)
  , DisplayMode(..)
  , AnimationState(..)
  , TooltipTarget(..)
  , getFlkBalance
  )

--------------------------------------------------------------------------------
-- | Main Render
--------------------------------------------------------------------------------

-- | Main render function
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

--------------------------------------------------------------------------------
-- | Container Classes
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- | Header
--------------------------------------------------------------------------------

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
        FlkOnly -> HH.text ""
        _ -> HH.text ""
    , renderAlertBadge state.alertLevel
    ]

getTitle :: DisplayMode -> String
getTitle = case _ of
  AllProviders -> "TOKEN BALANCE"
  VeniceOnly -> "DIEM BALANCE"
  FlkOnly -> "FLK BALANCE"
  Provider pid -> "BALANCE: " <> String.toUpper pid

--------------------------------------------------------------------------------
-- | Provider Selector
--------------------------------------------------------------------------------

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
    , HH.text "Other providers..."
    ]

providerButtonClasses :: Boolean -> Array H.ClassName
providerButtonClasses isActive =
  [ H.ClassName "provider-btn" ] <>
  if isActive then [ H.ClassName "provider-btn--active" ] else []

--------------------------------------------------------------------------------
-- | Balances
--------------------------------------------------------------------------------

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
          [ HH.span [ HP.class_ (H.ClassName "balance-icon") ] [ HH.text "o" ]
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
          [ HH.span [ HP.class_ (H.ClassName "balance-icon") ] [ HH.text "*" ]
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
        [ HH.span [ HP.class_ (H.ClassName "balance-icon") ] [ HH.text "#" ]
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

--------------------------------------------------------------------------------
-- | Token Metrics
--------------------------------------------------------------------------------

renderTokenMetrics :: forall m. State -> H.ComponentHTML Action () m
renderTokenMetrics state =
  HH.div
    [ HP.class_ (H.ClassName "balance-tracker__metrics") ]
    [ HH.div
        [ HP.class_ (H.ClassName "metric-card")
        , HE.onMouseEnter \_ -> ShowTooltip RateTooltip
        , HE.onMouseLeave \_ -> HideTooltip
        ]
        [ HH.span [ HP.class_ (H.ClassName "metric-icon") ] [ HH.text "v" ]
        , HH.span [ HP.class_ (H.ClassName "metric-value") ]
            [ HH.text $ formatConsumptionRate state.balance.consumptionRate ]
        , HH.span [ HP.class_ (H.ClassName "metric-label") ]
            [ HH.text "tokens/hr" ]
        ]
    , renderProjectionMetric state
    ]

renderProjectionMetric :: forall m. State -> H.ComponentHTML Action () m
renderProjectionMetric state = case state.displayMode of
  VeniceOnly ->
    HH.div
      [ HP.class_ (H.ClassName "metric-card")
      , HE.onMouseEnter \_ -> ShowTooltip ProjectionTooltip
      , HE.onMouseLeave \_ -> HideTooltip
      ]
      [ HH.span [ HP.class_ (H.ClassName "metric-icon") ] [ HH.text "T" ]
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
      [ HH.span [ HP.class_ (H.ClassName "metric-icon") ] [ HH.text "T" ]
      , HH.span [ HP.class_ (H.ClassName "metric-value") ]
          [ HH.text $ formatTimeToDepletionProjection state.balance.timeToDepletion ]
      , HH.span [ HP.class_ (H.ClassName "metric-label") ]
          [ HH.text "at current rate" ]
      ]
  _ ->
    HH.div
      [ HP.class_ (H.ClassName "metric-card") ]
      [ HH.span [ HP.class_ (H.ClassName "metric-icon") ] [ HH.text "$" ]
      , HH.span [ HP.class_ (H.ClassName "metric-value") ]
          [ HH.text $ formatUSD state.balance.costRate ]
      , HH.span [ HP.class_ (H.ClassName "metric-label") ]
          [ HH.text "cost/hr" ]
      ]

--------------------------------------------------------------------------------
-- | Cost Metrics
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- | Progress
--------------------------------------------------------------------------------

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
    dailyLimit = 1000000
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

--------------------------------------------------------------------------------
-- | Tooltip
--------------------------------------------------------------------------------

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
      VeniceOnly -> "Venice Diem Balance - Earned from staking VVV tokens. Resets daily."
      FlkOnly -> "FLK Balance - Fleek Token balance. Does not reset daily."
      _ -> "Balance - Current available balance."
  TokenTooltip -> "Token Usage - Total tokens consumed across all providers."
  CostTooltip -> "Total Cost - Cumulative cost across all providers."
  RateTooltip -> "Consumption Rate - Average tokens spent per hour."
  ProjectionTooltip -> "Time to Depletion - Estimated time until balance reaches zero."
  ProgressTooltip ->
    case displayMode of
      VeniceOnly -> "Today's Usage - Diem consumed today. Resets at midnight UTC."
      FlkOnly -> "Today's Usage - FLK consumed today."
      _ -> "Today's Usage - Tokens and cost consumed today."
  CountdownTooltip -> "Reset Countdown - Venice Diem resets at midnight UTC."
  ProviderTooltip -> "Provider Selection - Switch between providers."

--------------------------------------------------------------------------------
-- | Alert Badge
--------------------------------------------------------------------------------

renderAlertBadge :: forall m. AlertLevel -> H.ComponentHTML Action () m
renderAlertBadge = case _ of
  Normal -> HH.text ""
  Warning -> HH.span
    [ HP.class_ (H.ClassName "alert-badge alert-badge--warning") ]
    [ HH.text "!" ]
  Critical -> HH.span
    [ HP.class_ (H.ClassName "alert-badge alert-badge--critical") ]
    [ HH.text "!!" ]
  Depleted -> HH.span
    [ HP.class_ (H.ClassName "alert-badge alert-badge--depleted") ]
    [ HH.text "DEPLETED" ]

--------------------------------------------------------------------------------
-- | Actions
--------------------------------------------------------------------------------

renderActions :: forall m. State -> H.ComponentHTML Action () m
renderActions state =
  HH.div
    [ HP.class_ (H.ClassName "balance-tracker__actions") ]
    [ HH.button
        [ HP.classes [ H.ClassName "btn-icon" ]
        , HP.title "Refresh balance"
        , HE.onClick \_ -> RefreshBalance
        ]
        [ HH.text "R" ]
    , HH.button
        [ HP.classes [ H.ClassName "btn-icon" ]
        , HP.title "Settings"
        , HE.onClick \_ -> OpenSettings
        ]
        [ HH.text "S" ]
    ]

--------------------------------------------------------------------------------
-- | Helpers
--------------------------------------------------------------------------------

formatTimeToDepletionProjection :: Maybe Number -> String
formatTimeToDepletionProjection = case _ of
  Nothing -> "inf"
  Just hours -> formatTimeToDepletion hours

formatNumber :: Int -> String
formatNumber n = show n
