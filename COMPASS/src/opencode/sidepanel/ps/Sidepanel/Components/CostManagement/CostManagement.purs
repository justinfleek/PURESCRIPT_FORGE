{-|
Module      : Sidepanel.Components.CostManagement.CostManagement
Description : Main Halogen component for cost management UI

Main component displaying token usage, costs, budgets, and alerts.
-}
module Sidepanel.Components.CostManagement.CostManagement where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Sidepanel.Components.CostManagement.CostManagementTypes
  ( UsageSummary
  , BudgetStatus
  , UsageAlert
  , UsagePeriod(..)
  , AlertSeverity(..)
  )
import Sidepanel.Components.CostManagement.UsageTracker
  ( UsageTrackerState
  , initUsageTracker
  , getUsageSummary
  )
import Sidepanel.Components.CostManagement.BudgetManager
  ( BudgetManagerState
  , initBudgetManager
  , checkBudgetStatus
  , getAlerts
  )
import Effect.Ref (Ref)

-- | Component state
type State =
  { usageTracker :: Maybe (Ref UsageTrackerState)
  , budgetManager :: Maybe (Ref BudgetManagerState)
  , currentPeriod :: UsagePeriod
  , usageSummary :: Maybe UsageSummary
  , budgetStatus :: Maybe BudgetStatus
  , alerts :: Array UsageAlert
  }

-- | Component actions
data Action
  = Initialize
  | PeriodChanged UsagePeriod
  | RefreshData

-- | Component output
data Output
  = BudgetExceeded Number
  | BudgetWarning Number

-- | Component input
type Input = Unit

-- | Component factory
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \_ ->
      { usageTracker: Nothing
      , budgetManager: Nothing
      , currentPeriod: Today
      , usageSummary: Nothing
      , budgetStatus: Nothing
      , alerts: []
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

-- | Render component
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "cost-management theme-card") ]
    [ HH.h2
        [ HP.class_ (H.ClassName "theme-card-title") ]
        [ HH.text "Cost Management" ]
    , renderBudgetStatus state.budgetStatus
    , renderUsageSummary state.usageSummary
    , renderAlerts state.alerts
    , renderPeriodSelector state.currentPeriod
    ]

-- | Render budget status
renderBudgetStatus :: forall m. Maybe BudgetStatus -> H.ComponentHTML Action () m
renderBudgetStatus = case _ of
  Nothing -> HH.div_ [ HH.text "Loading budget status..." ]
  Just status ->
    HH.div
      [ HP.class_ (HH.ClassName "budget-status") ]
      [ HH.h3_ [ HH.text "Budget Status" ]
      , HH.div
          [ HP.class_ (HH.ClassName (if status.isExceeded then "exceeded" else if status.isNearLimit then "warning" else "ok")) ]
          [ HH.text ("Spent: $" <> show status.currentSpend)
          , case status.limit of
              Nothing -> HH.text " (No limit)"
              Just limit -> HH.text (" / $" <> show limit <> " (" <> show (status.percentageUsed * 100.0) <> "%)")
          ]
      , HH.div
          [ HP.class_ (HH.ClassName "progress-bar") ]
          [ HH.div
              [ HP.class_ (HH.ClassName "progress-fill")
              , HP.style ("width: " <> show (status.percentageUsed * 100.0) <> "%")
              ]
              []
          ]
      ]

-- | Render usage summary
renderUsageSummary :: forall m. Maybe UsageSummary -> H.ComponentHTML Action () m
renderUsageSummary = case _ of
  Nothing -> HH.div_ [ HH.text "Loading usage summary..." ]
  Just summary ->
    HH.div
      [ HP.class_ (HH.ClassName "usage-summary") ]
      [ HH.h3_ [ HH.text "Usage Summary" ]
      , HH.div
          [ HP.class_ (HH.ClassName "total-cost") ]
          [ HH.text ("Total Cost: $" <> show summary.totalCost) ]
      , HH.div
          [ HP.class_ (HH.ClassName "token-usage") ]
          [ HH.text ("Tokens: " <> show summary.totalUsage.totalTokens)
          , HH.text (" (Prompt: " <> show summary.totalUsage.promptTokens <> ", Completion: " <> show summary.totalUsage.completionTokens <> ")")
          ]
      , renderOperationBreakdown summary.operationBreakdown
      , renderModelBreakdown summary.modelBreakdown
      ]

-- | Render operation breakdown
renderOperationBreakdown :: forall m. Array { operation :: OperationType, count :: Int, usage :: TokenUsage, cost :: Number } -> H.ComponentHTML Action () m
renderOperationBreakdown breakdown =
  HH.div
    [ HP.class_ (HH.ClassName "operation-breakdown") ]
    [ HH.h4_ [ HH.text "By Operation" ]
    , HH.ul_ $ Array.map (\item ->
        HH.li_
          [ HH.text (showOperationType item.operation <> ": $" <> show item.cost <> " (" <> show item.count <> " operations)")
          ]
      ) breakdown
    ]

-- | Render model breakdown
renderModelBreakdown :: forall m. Array { modelId :: String, usage :: TokenUsage, cost :: Number } -> H.ComponentHTML Action () m
renderModelBreakdown breakdown =
  HH.div
    [ HP.class_ (HH.ClassName "model-breakdown") ]
    [ HH.h4_ [ HH.text "By Model" ]
    , HH.ul_ $ Array.map (\item ->
        HH.li_
          [ HH.text (item.modelId <> ": $" <> show item.cost)
          ]
      ) breakdown
    ]

-- | Render alerts
renderAlerts :: forall m. Array UsageAlert -> H.ComponentHTML Action () m
renderAlerts alerts =
  if Array.length alerts == 0 then
    HH.text ""
  else
    HH.div
      [ HP.class_ (HH.ClassName "alerts") ]
      [ HH.h3_ [ HH.text "Alerts" ]
      , HH.ul_ $ Array.map (\alert ->
          HH.li_
            [ HP.class_ (HH.ClassName (case alert.severity of Critical -> "critical"; Warning -> "warning"; Info -> "info")) ]
            [ HH.text alert.message ]
        ) alerts
      ]

-- | Render period selector
renderPeriodSelector :: forall m. UsagePeriod -> H.ComponentHTML Action () m
renderPeriodSelector currentPeriod =
  HH.div
    [ HP.class_ (HH.ClassName "period-selector") ]
    [ HH.button
        [ HP.class_ (HH.ClassName (if currentPeriod == Today then "active" else ""))
        , HE.onClick \_ -> PeriodChanged Today
        ]
        [ HH.text "Today" ]
    , HH.button
        [ HP.class_ (HH.ClassName (if currentPeriod == ThisWeek then "active" else ""))
        , HE.onClick \_ -> PeriodChanged ThisWeek
        ]
        [ HH.text "This Week" ]
    , HH.button
        [ HP.class_ (HH.ClassName (if currentPeriod == ThisMonth then "active" else ""))
        , HE.onClick \_ -> PeriodChanged ThisMonth
        ]
        [ HH.text "This Month" ]
    ]

-- | Handle actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Initialize tracker and budget manager
    tracker <- H.lift $ initUsageTracker
    budgetManager <- H.lift $ initBudgetManager defaultBudgetConfig
    
    H.modify_ \s -> s
      { usageTracker = Just tracker
      , budgetManager = Just budgetManager
      }
    
    -- Load initial data
    handleAction RefreshData
  
  PeriodChanged period -> do
    H.modify_ \s -> s { currentPeriod = period }
    handleAction RefreshData
  
  RefreshData -> do
    state <- H.get
    case state.usageTracker, state.budgetManager of
      Just tracker, Just budget -> do
        -- Get usage summary
        summary <- H.lift $ getUsageSummary tracker state.currentPeriod
        H.modify_ \s -> s { usageSummary = Just summary }
        
        -- Check budget status
        budgetStatus <- H.lift $ checkBudgetStatus budget tracker state.currentPeriod
        H.modify_ \s -> s { budgetStatus = Just budgetStatus }
        
        -- Get alerts
        alerts <- H.lift $ getAlerts budget
        H.modify_ \s -> s { alerts = alerts }
        
        -- Emit output if budget exceeded
        when budgetStatus.isExceeded do
          H.raise (BudgetExceeded budgetStatus.currentSpend)
        when budgetStatus.isNearLimit do
          H.raise (BudgetWarning budgetStatus.currentSpend)
      _, _ -> pure unit

-- | Show operation type
showOperationType :: OperationType -> String
showOperationType = case _ of
  InlineSuggestion -> "Inline Suggestions"
  CodeReview -> "Code Review"
  Refactoring -> "Refactoring"
  TestGeneration -> "Test Generation"
  ErrorAnalysis -> "Error Analysis"
  ChatCompletion -> "Chat Completion"
  OtherOperation name -> name

-- | Default budget config
defaultBudgetConfig :: BudgetConfig
defaultBudgetConfig =
  { dailyLimit: Just 10.0
  , weeklyLimit: Just 50.0
  , monthlyLimit: Just 200.0
  , alertThreshold: 0.8  -- Alert at 80%
  , currency: "USD"
  }

-- | Import utilities
import Halogen.HTML.Events as HE
import Effect.Aff (when)
import Sidepanel.Components.CostManagement.CostManagementTypes (BudgetConfig, OperationType(..))
