{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

-- | Bridge Alerts System
-- |
-- | Alert management system with configurable rules, severity levels,
-- | and automatic evaluation against Prometheus metrics.
-- | Supports firing, resolving, and pending alert states.
-- |
-- | Dependencies:
-- | - Bridge.Metrics.Prometheus: MetricRegistry for metric evaluation
-- | - Bridge.Error.CircuitBreaker: CircuitBreaker health checks
-- | - Control.Concurrent.STM: Concurrent state management
-- | - Data.Map: Alert storage
-- | - Data.Time: Timestamps
module Bridge.Alerts.System where

import Bridge.Metrics.Prometheus (MetricRegistry, exportMetrics)
import Bridge.Error.CircuitBreaker (CircuitBreaker, isAvailable)
import Control.Concurrent.STM (TVar, newTVarIO, readTVar, writeTVar, atomically)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import Data.Time (UTCTime, getCurrentTime, diffUTCTime)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)

-- | Alert severity levels
data AlertSeverity
  = Info
  | Warning
  | Critical
  deriving (Eq, Ord, Show)

-- | Alert state
data AlertState
  = Firing
  | Resolved
  | Pending
  deriving (Eq, Show)

-- | Alert rule configuration
data AlertRule = AlertRule
  { arName :: Text
  , arDescription :: Text
  , arSeverity :: AlertSeverity
  , arMetricName :: Text
  , arThreshold :: Double
  , arComparison :: Text -- "gt", "lt", "eq", "gte", "lte"
  , arForDuration :: Int -- seconds the condition must hold before firing
  }
  deriving (Eq, Show)

-- | Alert instance
data Alert = Alert
  { alertName :: Text
  , alertDescription :: Text
  , alertSeverity :: AlertSeverity
  , alertState :: AlertState
  , alertFiredAt :: UTCTime
  , alertResolvedAt :: Maybe UTCTime
  , alertValue :: Double
  , alertThreshold :: Double
  }
  deriving (Eq, Show)

-- | Alert manager
data AlertManager = AlertManager
  { amRules :: [AlertRule]
  , amActiveAlerts :: TVar (Map Text Alert)
  , amPendingSince :: TVar (Map Text UTCTime)
  , amMetricRegistry :: MetricRegistry
  , amNotificationCallback :: Alert -> IO ()
  }

-- | Alert configuration (list of rules)
type AlertConfig = [AlertRule]

-- | Default alert rules
-- |
-- | Provides 3 standard rules:
-- | 1. High error rate (> 10% of requests)
-- | 2. High latency (> 5000ms average)
-- | 3. Circuit breaker open (failure count > 0)
defaultAlertRules :: AlertConfig
defaultAlertRules =
  [ AlertRule
      { arName = "high_error_rate"
      , arDescription = "Error rate exceeds 10% of total requests"
      , arSeverity = Critical
      , arMetricName = "bridge_error_rate"
      , arThreshold = 0.1
      , arComparison = "gt"
      , arForDuration = 60
      }
  , AlertRule
      { arName = "high_latency"
      , arDescription = "Average request latency exceeds 5000ms"
      , arSeverity = Warning
      , arMetricName = "bridge_avg_latency_ms"
      , arThreshold = 5000.0
      , arComparison = "gt"
      , arForDuration = 120
      }
  , AlertRule
      { arName = "circuit_breaker_open"
      , arDescription = "Circuit breaker has tripped open due to failures"
      , arSeverity = Critical
      , arMetricName = "bridge_circuit_breaker_failures"
      , arThreshold = 0.0
      , arComparison = "gt"
      , arForDuration = 0
      }
  ]

-- | Create alert manager
-- |
-- | Initializes the alert manager with the given rules,
-- | metric registry, and notification callback.
createAlertManager
  :: AlertConfig
  -> MetricRegistry
  -> (Alert -> IO ())
  -> IO AlertManager
createAlertManager rules registry callback = do
  activeAlerts <- newTVarIO Map.empty
  pendingSince <- newTVarIO Map.empty
  pure AlertManager
    { amRules = rules
    , amActiveAlerts = activeAlerts
    , amPendingSince = pendingSince
    , amMetricRegistry = registry
    , amNotificationCallback = callback
    }

-- | Evaluate all alert rules against current metrics
-- |
-- | Checks each rule, transitions alerts between
-- | Pending -> Firing -> Resolved states, and triggers
-- | notifications on state changes.
evaluateAlerts :: AlertManager -> IO [Alert]
evaluateAlerts manager = do
  now <- getCurrentTime
  results <- mapM (evaluateRule manager now) (amRules manager)
  pure (concat results)

-- | Evaluate a single alert rule
-- |
-- | Compares the current metric value against the rule threshold.
-- | Manages the pending duration before firing.
evaluateRule :: AlertManager -> UTCTime -> AlertRule -> IO [Alert]
evaluateRule manager now rule = do
  -- Read current metric value (stub: parse from exported metrics)
  -- In production, this would read directly from the MetricRegistry
  metricText <- exportMetrics (amMetricRegistry manager)
  let metricValue = extractMetricValue (arMetricName rule) metricText
  let conditionMet = compareValue (arComparison rule) metricValue (arThreshold rule)

  activeAlerts <- atomically (readTVar (amActiveAlerts manager))
  pendingSince <- atomically (readTVar (amPendingSince manager))

  let ruleName = arName rule

  if conditionMet
    then do
      -- Check if already firing
      case Map.lookup ruleName activeAlerts of
        Just existing ->
          if alertState existing == Firing
            then pure [] -- Already firing, no change
            else do
              -- Transition to firing
              let fired = existing { alertState = Firing, alertValue = metricValue }
              atomically (writeTVar (amActiveAlerts manager) (Map.insert ruleName fired activeAlerts))
              sendAlert manager fired
              pure [fired]
        Nothing -> do
          -- Check pending duration
          case Map.lookup ruleName pendingSince of
            Just pendingStart -> do
              let elapsed = realToFrac (diffUTCTime now pendingStart) :: Double
              if elapsed >= fromIntegral (arForDuration rule)
                then do
                  -- Fire the alert
                  let alert = Alert
                        { alertName = ruleName
                        , alertDescription = arDescription rule
                        , alertSeverity = arSeverity rule
                        , alertState = Firing
                        , alertFiredAt = now
                        , alertResolvedAt = Nothing
                        , alertValue = metricValue
                        , alertThreshold = arThreshold rule
                        }
                  atomically $ do
                    writeTVar (amActiveAlerts manager) (Map.insert ruleName alert activeAlerts)
                    writeTVar (amPendingSince manager) (Map.delete ruleName pendingSince)
                  sendAlert manager alert
                  pure [alert]
                else
                  pure [] -- Still pending
            Nothing -> do
              -- Start pending
              atomically (writeTVar (amPendingSince manager) (Map.insert ruleName now pendingSince))
              pure []
    else do
      -- Condition not met: resolve if active
      case Map.lookup ruleName activeAlerts of
        Just existing ->
          if alertState existing == Firing
            then do
              let resolved = existing
                    { alertState = Resolved
                    , alertResolvedAt = Just now
                    }
              atomically $ do
                writeTVar (amActiveAlerts manager) (Map.insert ruleName resolved activeAlerts)
                writeTVar (amPendingSince manager) (Map.delete ruleName pendingSince)
              sendAlert manager resolved
              pure [resolved]
            else pure []
        Nothing -> do
          -- Clear any pending state
          atomically (writeTVar (amPendingSince manager) (Map.delete ruleName pendingSince))
          pure []

-- | Send alert notification
sendAlert :: AlertManager -> Alert -> IO ()
sendAlert manager alert = amNotificationCallback manager alert

-- | Extract metric value from Prometheus text format
-- |
-- | Searches exported metrics text for the named metric
-- | and parses its numeric value.
extractMetricValue :: Text -> Text -> Double
extractMetricValue metricName metricsText =
  let linesOfText = T.lines metricsText
      matchingLines = filter (T.isPrefixOf metricName) linesOfText
  in case matchingLines of
    [] -> 0.0
    (line:_) ->
      let parts = T.words line
      in case parts of
        [_, valueText] ->
          case reads (T.unpack valueText) of
            [(v, "")] -> v
            _ -> 0.0
        _ -> 0.0

-- | Compare a value against a threshold using the given comparison operator
compareValue :: Text -> Double -> Double -> Bool
compareValue "gt" actual threshold = actual > threshold
compareValue "lt" actual threshold = actual < threshold
compareValue "eq" actual threshold = abs (actual - threshold) < 1.0e-9
compareValue "gte" actual threshold = actual >= threshold
compareValue "lte" actual threshold = actual <= threshold
compareValue _ _ _ = False
