{-|
Module      : Sidepanel.Components.CostManagement.BudgetManager
Description : Manage budgets and alerts
Manages budget limits, tracks spending, and generates alerts.
-}
module Sidepanel.Components.CostManagement.BudgetManager where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Class (liftEffect)
import Sidepanel.Components.CostManagement.CostManagementTypes
  ( BudgetConfig
  , BudgetStatus
  , UsagePeriod(..)
  , UsageAlert
  , AlertType(..)
  , AlertSeverity(..)
  )
import Sidepanel.Components.CostManagement.UsageTracker (getUsageSummary)

-- | Budget manager state
type BudgetManagerState =
  { config :: BudgetConfig
  , alerts :: Array UsageAlert
  }

-- | Initialize budget manager
initBudgetManager :: BudgetConfig -> Aff (Ref BudgetManagerState)
initBudgetManager config = do
  liftEffect $ Ref.new
    { config: config
    , alerts: []
    }

-- | Check budget status
checkBudgetStatus
  :: Ref BudgetManagerState
  -> Ref UsageTrackerState
  -> UsagePeriod
  -> Aff BudgetStatus
checkBudgetStatus budgetRef trackerRef period = do
  budgetState <- liftEffect $ Ref.read budgetRef
  summary <- UsageTracker.getUsageSummary trackerRef period
  
  -- Get limit for period
  let limit = getLimitForPeriod budgetState.config period
  
  -- Calculate percentage used
  let percentageUsed = case limit of
        Nothing -> 0.0
        Just lim -> summary.totalCost / lim
  
  -- Check if exceeded or near limit
  let isExceeded = case limit of
        Nothing -> false
        Just lim -> summary.totalCost >= lim
  
  let isNearLimit = case limit of
        Nothing -> false
        Just lim -> percentageUsed >= budgetState.config.alertThreshold
  
  -- Generate alert if needed
  when (isExceeded || isNearLimit) do
    generateAlert budgetRef period summary.totalCost limit isExceeded
  
  pure
    { config: budgetState.config
    , currentPeriod: period
    , currentSpend: summary.totalCost
    , limit: limit
    , percentageUsed: percentageUsed
    , isExceeded: isExceeded
    , isNearLimit: isNearLimit
    }

-- | Get limit for period
getLimitForPeriod :: BudgetConfig -> UsagePeriod -> Maybe Number
getLimitForPeriod config period =
  case period of
    Today -> config.dailyLimit
    ThisWeek -> config.weeklyLimit
    ThisMonth -> config.monthlyLimit
    LastMonth -> config.monthlyLimit  -- Use monthly limit
    CustomPeriod _ -> Nothing  -- No limit for custom periods

-- | Generate alert
generateAlert
  :: Ref BudgetManagerState
  -> UsagePeriod
  -> Number
  -> Maybe Number
  -> Boolean
  -> Aff Unit
generateAlert budgetRef period currentSpend limitM isExceeded = do
  timestamp <- liftEffect getCurrentTimestamp
  
  case limitM of
    Nothing -> pure unit
    Just limit -> do
      let alertType = if isExceeded then BudgetExceeded else BudgetWarning
      let severity = if isExceeded then Critical else Warning
      let message = if isExceeded then
            "Budget exceeded! Current spend: $" <> show currentSpend <> " (Limit: $" <> show limit <> ")"
          else
            "Approaching budget limit. Current spend: $" <> show currentSpend <> " (Limit: $" <> show limit <> ")"
      
      let alert =
            { alertType: alertType
            , message: message
            , severity: severity
            , timestamp: timestamp
            , currentSpend: currentSpend
            , limit: limit
            }
      
      liftEffect $ Ref.modify_ (\s -> s { alerts = s.alerts <> [alert] }) budgetRef

-- | Get alerts
getAlerts :: Ref BudgetManagerState -> Aff (Array UsageAlert)
getAlerts budgetRef = do
  state <- liftEffect $ Ref.read budgetRef
  pure state.alerts

-- | Clear alerts
clearAlerts :: Ref BudgetManagerState -> Aff Unit
clearAlerts budgetRef = do
  liftEffect $ Ref.modify_ (\s -> s { alerts = [] }) budgetRef

-- | Import types
import Sidepanel.Components.CostManagement.UsageTracker (UsageTrackerState)
import Effect.Aff (when)
import Sidepanel.Components.CostManagement.CostManagementTypes (UsageSummary)
import Sidepanel.Components.CostManagement.UsageTracker (getUsageSummary) as UsageTracker
foreign import getCurrentTimestamp :: Effect Number
