{-|
Module      : Sidepanel.Components.CostManagement.CostManagementTypes
Description : Types for cost management and token usage tracking
Types for tracking token usage, calculating costs, and managing budgets.
-}
module Sidepanel.Components.CostManagement.CostManagementTypes where

import Prelude

-- | Token usage record
type TokenUsage =
  { promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  , cacheReadTokens :: Int
  , cacheWriteTokens :: Int
  }

-- | Cost calculation
type CostCalculation =
  { inputCost :: Number
  , outputCost :: Number
  , cacheCost :: Number
  , totalCost :: Number
  , currency :: String
  }

-- | Usage session (tracks usage over time period)
type UsageSession =
  { sessionId :: String
  , startTime :: Number  -- Timestamp
  , endTime :: Maybe Number
  , usage :: TokenUsage
  , cost :: CostCalculation
  , operation :: OperationType
  , modelId :: String
  }

-- | Operation type
data OperationType
  = InlineSuggestion
  | CodeReview
  | Refactoring
  | TestGeneration
  | ErrorAnalysis
  | ChatCompletion
  | OtherOperation String

derive instance eqOperationType :: Eq OperationType

-- | Usage summary (aggregated over period)
type UsageSummary =
  { period :: UsagePeriod
  , totalUsage :: TokenUsage
  , totalCost :: Number
  , operationBreakdown :: Array OperationSummary
  , modelBreakdown :: Array ModelSummary
  }

-- | Usage period
data UsagePeriod
  = Today
  | ThisWeek
  | ThisMonth
  | LastMonth
  | CustomPeriod { start :: Number, end :: Number }

derive instance eqUsagePeriod :: Eq UsagePeriod

-- | Operation summary
type OperationSummary =
  { operation :: OperationType
  , count :: Int
  , usage :: TokenUsage
  , cost :: Number
  }

-- | Model summary
type ModelSummary =
  { modelId :: String
  , usage :: TokenUsage
  , cost :: Number
  }

-- | Budget configuration
type BudgetConfig =
  { dailyLimit :: Maybe Number
  , weeklyLimit :: Maybe Number
  , monthlyLimit :: Maybe Number
  , alertThreshold :: Number  -- Percentage (0.0 to 1.0)
  , currency :: String
  }

-- | Budget status
type BudgetStatus =
  { config :: BudgetConfig
  , currentPeriod :: UsagePeriod
  , currentSpend :: Number
  , limit :: Maybe Number
  , percentageUsed :: Number  -- 0.0 to 1.0
  , isExceeded :: Boolean
  , isNearLimit :: Boolean  -- Within alert threshold
  }

-- | Cost projection (estimate before execution)
type CostProjection =
  { estimatedTokens :: TokenUsage
  , estimatedCost :: Number
  , confidence :: Number  -- 0.0 to 1.0
  , modelId :: String
  , operation :: OperationType
  }

-- | Usage alert
type UsageAlert =
  { alertType :: AlertType
  , message :: String
  , severity :: AlertSeverity
  , timestamp :: Number
  , currentSpend :: Number
  , limit :: Number
  }

-- | Alert type
data AlertType
  = BudgetExceeded
  | BudgetWarning  -- Near limit
  | HighUsageRate  -- Unusually high usage
  | CostAnomaly  -- Unexpected cost spike

derive instance eqAlertType :: Eq AlertType

-- | Alert severity
data AlertSeverity
  = Critical
  | Warning
  | Info

derive instance eqAlertSeverity :: Eq AlertSeverity
