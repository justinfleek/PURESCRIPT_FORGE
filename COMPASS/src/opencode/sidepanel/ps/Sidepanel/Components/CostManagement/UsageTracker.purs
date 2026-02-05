{-|
Module      : Sidepanel.Components.CostManagement.UsageTracker
Description : Track token usage across sessions
Tracks token usage and costs across all operations.
-}
module Sidepanel.Components.CostManagement.UsageTracker where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Effect.Class (liftEffect)
import Sidepanel.Components.CostManagement.CostManagementTypes
  ( UsageSession
  , TokenUsage
  , CostCalculation
  , OperationType
  , UsageSummary
  , UsagePeriod(..)
  )
import Sidepanel.Components.CostManagement.CostCalculator (calculateCost)
import Opencode.Provider.Provider (Model)

-- | Usage tracker state
type UsageTrackerState =
  { sessions :: Array UsageSession
  , currentSession :: Maybe String
  }

-- | Initialize usage tracker
initUsageTracker :: Aff (Ref UsageTrackerState)
initUsageTracker = do
  liftEffect $ Ref.new
    { sessions: []
    , currentSession: Nothing
    }

-- | Record token usage
recordUsage
  :: Ref UsageTrackerState
  -> Model
  -> TokenUsage
  -> OperationType
  -> Aff UsageSession
recordUsage trackerRef model usage operation = do
  -- Calculate cost
  let cost = calculateCost model usage
  
  -- Create session
  timestamp <- liftEffect getCurrentTimestamp
  let sessionId = generateSessionId timestamp
  
  let session =
        { sessionId: sessionId
        , startTime: timestamp
        , endTime: Just timestamp
        , usage: usage
        , cost: cost
        , operation: operation
        , modelId: model.id
        }
  
  -- Add to tracker
  liftEffect $ Ref.modify_ (\s -> s { sessions = s.sessions <> [session] }) trackerRef
  
  pure session

-- | Get usage summary for period
getUsageSummary
  :: Ref UsageTrackerState
  -> UsagePeriod
  -> Aff UsageSummary
getUsageSummary trackerRef period = do
  state <- liftEffect $ Ref.read trackerRef
  
  -- Filter sessions by period
  let periodSessions = filterSessionsByPeriod state.sessions period
  
  -- Aggregate usage
  let totalUsage = aggregateUsage periodSessions
  let totalCost = Array.foldl (\acc s -> acc + s.cost.totalCost) 0.0 periodSessions
  
  -- Breakdown by operation
  let operationBreakdown = breakdownByOperation periodSessions
  
  -- Breakdown by model
  let modelBreakdown = breakdownByModel periodSessions
  
  pure
    { period: period
    , totalUsage: totalUsage
    , totalCost: totalCost
    , operationBreakdown: operationBreakdown
    , modelBreakdown: modelBreakdown
    }

-- | Filter sessions by period
filterSessionsByPeriod :: Array UsageSession -> UsagePeriod -> Array UsageSession
filterSessionsByPeriod sessions period =
  let now = 0.0  -- Would get actual current time
      periodStart = getPeriodStart period now
      periodEnd = getPeriodEnd period now
  in
    Array.filter (\s -> s.startTime >= periodStart && (case s.endTime of Nothing -> false; Just end -> end <= periodEnd)) sessions

-- | Get period start timestamp
getPeriodStart :: UsagePeriod -> Number -> Number
getPeriodStart period now =
  case period of
    Today -> now - (24.0 * 60.0 * 60.0 * 1000.0)  -- 24 hours ago
    ThisWeek -> now - (7.0 * 24.0 * 60.0 * 60.0 * 1000.0)  -- 7 days ago
    ThisMonth -> now - (30.0 * 24.0 * 60.0 * 60.0 * 1000.0)  -- 30 days ago
    LastMonth -> now - (60.0 * 24.0 * 60.0 * 60.0 * 1000.0)  -- 60 days ago
    CustomPeriod { start } -> start

-- | Get period end timestamp
getPeriodEnd :: UsagePeriod -> Number -> Number
getPeriodEnd period now =
  case period of
    CustomPeriod { end } -> end
    _ -> now

-- | Aggregate usage across sessions
aggregateUsage :: Array UsageSession -> TokenUsage
aggregateUsage sessions =
  Array.foldl (\acc s ->
    { promptTokens: acc.promptTokens + s.usage.promptTokens
    , completionTokens: acc.completionTokens + s.usage.completionTokens
    , totalTokens: acc.totalTokens + s.usage.totalTokens
    , cacheReadTokens: acc.cacheReadTokens + s.usage.cacheReadTokens
    , cacheWriteTokens: acc.cacheWriteTokens + s.usage.cacheWriteTokens
    }
  )
    { promptTokens: 0
    , completionTokens: 0
    , totalTokens: 0
    , cacheReadTokens: 0
    , cacheWriteTokens: 0
    }
    sessions

-- | Breakdown by operation type
breakdownByOperation :: Array UsageSession -> Array { operation :: OperationType, count :: Int, usage :: TokenUsage, cost :: Number }
breakdownByOperation sessions =
  -- Group by operation type manually
  let operationMap = Array.foldl (\acc session ->
        let key = session.operation
            existing = Array.find (\item -> item.operation == key) acc
        in
          case existing of
            Nothing -> acc <> [{ operation: key, count: 1, usage: session.usage, cost: session.cost.totalCost }]
            Just item -> 
              -- Find all sessions with this operation to aggregate properly
              let matchingSessions = Array.filter (\s -> s.operation == key) (sessions)
                  aggregatedUsage = aggregateUsage matchingSessions
              in
                Array.map (\i -> if i.operation == key then
                    { operation: i.operation
                    , count: Array.length matchingSessions
                    , usage: aggregatedUsage
                    , cost: Array.foldl (\sum s -> sum + s.cost.totalCost) 0.0 matchingSessions
                    }
                  else i
                ) acc
      ) [] sessions
  in
    operationMap

-- | Breakdown by model
breakdownByModel :: Array UsageSession -> Array { modelId :: String, usage :: TokenUsage, cost :: Number }
breakdownByModel sessions =
  -- Group by model ID manually
  let modelMap = Array.foldl (\acc session ->
        let key = session.modelId
            existing = Array.find (\item -> item.modelId == key) acc
        in
          case existing of
            Nothing -> acc <> [{ modelId: key, usage: session.usage, cost: session.cost.totalCost }]
            Just item ->
              -- Find all sessions with this model to aggregate properly
              let matchingSessions = Array.filter (\s -> s.modelId == key) sessions
                  aggregatedUsage = aggregateUsage matchingSessions
              in
                Array.map (\i -> if i.modelId == key then
                    { modelId: i.modelId
                    , usage: aggregatedUsage
                    , cost: Array.foldl (\sum s -> sum + s.cost.totalCost) 0.0 matchingSessions
                    }
                  else i
                ) acc
      ) [] sessions
  in
    modelMap

-- | Generate session ID
generateSessionId :: Number -> String
generateSessionId timestamp = "session-" <> show timestamp

-- | Get current timestamp
foreign import getCurrentTimestamp :: Effect Number
