-- | Comprehensive Balance and Token Tracking - Multi-Provider Balance Management
-- |
-- | **What:** Provides comprehensive balance tracking supporting multiple providers,
-- |         with Venice Diem as a Venice-specific option. Tracks token usage, costs,
-- |         consumption rates, and alert levels.
-- | **Why:** Enables unified balance tracking across different AI providers while
-- |         supporting provider-specific features (e.g., Venice Diem system). Provides
-- |         consumption rate calculations and depletion warnings.
-- | **How:** Maintains provider-specific balances in a Map, aggregates metrics across
-- |         all providers, and calculates alert levels based on thresholds and depletion
-- |         estimates.
-- |
-- | **Dependencies:**
-- | - `Data.Map`: For provider balance storage
-- | - `Data.DateTime`: For timestamp tracking
-- |
-- | **Mathematical Foundation:**
-- | - **Consumption Rate:** `consumptionRate = tokensUsed / timeElapsed` (tokens per hour)
-- | - **Time to Depletion:** `timeToDepletion = balance / consumptionRate` (hours)
-- | - **Alert Levels:** Calculated from balance thresholds and time to depletion:
-- |   - `Depleted`: Balance <= 0
-- |   - `Critical`: Balance < 1.0 Diem OR timeToDepletion < 0.5 hours
-- |   - `Warning`: Balance < 5.0 Diem OR timeToDepletion < 2.0 hours
-- |   - `Normal`: Otherwise
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.State.Balance as Balance
-- |
-- | -- Get initial balance state
-- | balance :: Balance.BalanceState
-- | balance = Balance.initialBalanceState
-- |
-- | -- Calculate alert level
-- | alertLevel = Balance.calculateAlertLevel balance
-- | ```
-- |
-- | Based on specs 11-DIEM-TRACKING.md, 13-TOKEN-USAGE-METRICS.md
module Sidepanel.State.Balance where

import Prelude
import Data.DateTime (DateTime)
import Data.Maybe (Maybe)
import Data.Map as Map

-- | Provider identifier
type ProviderId = String

-- | Token type (for providers that have different token types)
data TokenType
  = PromptTokens
  | CompletionTokens
  | CachedTokens  -- Venice-specific
  | TotalTokens

derive instance eqTokenType :: Eq TokenType

-- | Provider-specific balance
type ProviderBalance =
  { providerId :: ProviderId
  , providerName :: String
  , balance :: BalanceAmount
  , tokenUsage :: TokenUsage
  , cost :: Number
  , lastUpdated :: Maybe DateTime
  }

-- | Balance amount (supports different balance types)
data BalanceAmount
  = DiemBalance Number      -- Venice Diem
  | FlkBalance Number       -- Fleek Token (FLK)
  | UsdBalance Number       -- Venice USD or other USD credits
  | CreditBalance Number    -- Generic credits
  | TokenBalance Number     -- Token-based balance
  | Unlimited              -- Unlimited usage

derive instance eqBalanceAmount :: Eq BalanceAmount

-- | Token usage metrics
type TokenUsage =
  { promptTokens :: Int
  , completionTokens :: Int
  , cachedTokens :: Int      -- Venice-specific
  , totalTokens :: Int
  }

-- | Comprehensive balance state
type BalanceState =
  { -- Provider-specific balances
    providerBalances :: Map.Map ProviderId ProviderBalance
  
  -- Venice-specific (Diem system)
  , venice :: Maybe VeniceBalance
  
  -- FLK (Fleek Token) balance - Independent payment method
  , flk :: Maybe FlkBalance
  
  -- Aggregated metrics (all providers)
  , totalTokens :: TokenUsage
  , totalCost :: Number
  , totalCostToday :: Number
  
  -- Consumption metrics
  , consumptionRate :: Number      -- Tokens per hour
  , costRate :: Number            -- USD per hour
  , timeToDepletion :: Maybe Number -- Hours (Venice-specific)
  
  -- Today's usage
  , todayUsed :: TokenUsage
  , todayCost :: Number
  
  -- Alert state
  , alertLevel :: AlertLevel
  , lastUpdated :: Maybe DateTime
  }

-- | Venice-specific balance (Diem system)
type VeniceBalance =
  { diem :: Number
  , usd :: Number
  , effective :: Number
  , todayUsed :: Number
  , todayStartBalance :: Number
  , resetCountdown :: Maybe DateTime  -- UTC midnight
  }

-- | FLK (Fleek Token) balance - Independent payment method
type FlkBalance =
  { flk :: Number
  , effective :: Number      -- FLK balance (1 FLK = 1 API credit equivalent)
  , todayUsed :: Number
  , todayStartBalance :: Number
  }

data AlertLevel = Normal | Warning | Critical | Depleted

derive instance eqAlertLevel :: Eq AlertLevel
derive instance ordAlertLevel :: Ord AlertLevel

-- | Initial balance state
initialBalanceState :: BalanceState
initialBalanceState =
  { providerBalances: Map.empty
  , venice: Nothing
  , flk: Nothing
  , totalTokens:
      { promptTokens: 0
      , completionTokens: 0
      , cachedTokens: 0
      , totalTokens: 0
      }
  , totalCost: 0.0
  , totalCostToday: 0.0
  , consumptionRate: 0.0
  , costRate: 0.0
  , timeToDepletion: Nothing
  , todayUsed:
      { promptTokens: 0
      , completionTokens: 0
      , cachedTokens: 0
      , totalTokens: 0
      }
  , todayCost: 0.0
  , alertLevel: Normal
  , lastUpdated: Nothing
  }

-- | Calculate alert level from balance state - Determine alert severity
-- |
-- | **Purpose:** Calculates the appropriate alert level based on balance thresholds
-- |             and time to depletion. Checks FLK balance first, then Venice balance,
-- |             then generic cost thresholds.
-- | **Parameters:**
-- | - `state`: Current balance state
-- | **Returns:** AlertLevel (Normal, Warning, Critical, or Depleted)
-- | **Side Effects:** None (pure function)
-- |
-- | **Alert Logic:**
-- | - **FLK Balance Present (checked first):**
-- |   - `Depleted`: FLK <= 0
-- |   - `Critical`: FLK < 1.0
-- |   - `Warning`: FLK < 5.0
-- |   - `Normal`: Otherwise
-- | - **Venice Balance Present (if no FLK):**
-- |   - `Depleted`: Diem <= 0
-- |   - `Critical`: Diem < 1.0 OR timeToDepletion < 0.5 hours
-- |   - `Warning`: Diem < 5.0 OR timeToDepletion < 2.0 hours
-- |   - `Normal`: Otherwise
-- | - **No Balance (fallback):**
-- |   - `Critical`: Total cost today > $200
-- |   - `Warning`: Total cost today > $100
-- |   - `Normal`: Otherwise
-- |
-- | **Example:**
-- | ```purescript
-- | alertLevel = calculateAlertLevel currentBalance
-- | ```
calculateAlertLevel :: BalanceState -> AlertLevel
calculateAlertLevel state = 
  -- Check FLK balance first (if present)
  case state.flk of
    Just flkBalance ->
      -- FLK-specific alerts
      if flkBalance.flk <= 0.0 then Depleted
      else if flkBalance.flk < 1.0 then Critical
      else if flkBalance.flk < 5.0 then Warning
      else Normal
    Nothing ->
      -- Check Venice balance (if present)
      case state.venice of
        Just venice ->
          -- Venice-specific alerts (Diem-based)
          if venice.diem <= 0.0 then Depleted
          else if venice.diem < 1.0 then Critical
          else if venice.diem < 5.0 then Warning
          else if isTimeCritical state then Critical
          else if isTimeWarning state then Warning
          else Normal
        Nothing ->
          -- Generic alerts based on cost/tokens
          if state.totalCostToday > 100.0 then Warning  -- $100/day threshold
          else if state.totalCostToday > 200.0 then Critical
          else Normal

-- | Check if time to depletion is critical - Less than 30 minutes
-- |
-- | **Purpose:** Determines if time to depletion is critical (< 30 minutes).
-- | **Parameters:**
-- | - `state`: Current balance state
-- | **Returns:** True if time to depletion is critical, false otherwise
-- | **Side Effects:** None (pure function)
isTimeCritical :: BalanceState -> Boolean
isTimeCritical state = case state.timeToDepletion of
  Nothing -> false
  Just hours -> hours < 0.5  -- Less than 30 minutes

-- | Check if time to depletion is warning - Less than 2 hours
-- |
-- | **Purpose:** Determines if time to depletion is at warning level (< 2 hours).
-- | **Parameters:**
-- | - `state`: Current balance state
-- | **Returns:** True if time to depletion is at warning level, false otherwise
-- | **Side Effects:** None (pure function)
isTimeWarning :: BalanceState -> Boolean
isTimeWarning state = case state.timeToDepletion of
  Nothing -> false
  Just hours -> hours < 2.0  -- Less than 2 hours
