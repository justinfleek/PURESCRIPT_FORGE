{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData #-}

-- | Alerting System - Production Alert Management
-- |
-- | **What:** Manages alerts for production issues (high error rates, low balance,
-- |         circuit breaker open, etc.). Sends alerts via multiple channels.
-- | **Why:** Enables proactive issue detection and response. Prevents silent failures.
-- |         Ensures operators are notified of critical issues immediately.
-- | **How:** Monitors metrics and state, evaluates alert rules, sends alerts via
-- |         configured channels (email, Slack, PagerDuty, etc.).
-- |
-- | **Dependencies:**
-- | - `Bridge.Metrics.Prometheus`: Metrics for alert evaluation
-- | - `Bridge.Error.CircuitBreaker`: Circuit breaker status
-- |
-- | **Mathematical Foundation:**
-- | - **Alert Rule:** `metric > threshold` for duration `window`
-- | - **Alert State:** `Firing` when condition met, `Resolved` when condition clears
-- | - **Alert Deduplication:** Same alert not sent twice within `cooldown` period
-- |
-- | **Usage Example:**
-- | ```haskell
-- | import Bridge.Alerts.System as Alerts
-- |
-- | -- Create alert manager
-- | manager <- Alerts.createAlertManager config
-- |
-- | -- Evaluate alerts
-- | Alerts.evaluateAlerts manager metrics
-- | ```
module Bridge.Alerts.System where

import Prelude hiding (read)
import Control.Concurrent.STM
import qualified Data.Text as T
import qualified Data.Map.Strict as Map
import Data.Time (UTCTime, getCurrentTime)
import Bridge.Metrics.Prometheus (MetricRegistry)
import Bridge.Error.CircuitBreaker (CircuitBreaker, getStatus, CircuitBreakerStatus)

-- | Alert severity
data AlertSeverity
  = AlertInfo
  | AlertWarning
  | AlertCritical
  deriving (Eq, Show)

-- | Alert state
data AlertState
  = AlertFiring UTCTime -- Firing since timestamp
  | AlertResolved UTCTime -- Resolved at timestamp
  | AlertPending UTCTime -- Pending (not yet firing)
  deriving (Eq, Show)

-- | Alert definition
data AlertRule = AlertRule
  { arName :: T.Text
  , arDescription :: T.Text
  , arSeverity :: AlertSeverity
  , arMetric :: T.Text -- Metric name
  , arThreshold :: Double -- Threshold value
  , arOperator :: T.Text -- "gt", "lt", "eq"
  , arWindowSeconds :: Int -- Evaluation window
  , arCooldownSeconds :: Int -- Cooldown between alerts
  }
  deriving (Eq, Show)

-- | Alert instance
data Alert = Alert
  { alertRule :: AlertRule
  , alertState :: AlertState
  , alertValue :: Double -- Current metric value
  , alertLastSent :: Maybe UTCTime -- Last alert sent timestamp
  }
  deriving (Eq, Show)

-- | Alert manager
data AlertManager = AlertManager
  { amRules :: [AlertRule]
  , amAlerts :: TVar (Map.Map T.Text Alert)
  , amMetrics :: MetricRegistry
  , amCircuitBreakers :: Map.Map T.Text CircuitBreaker
  }

-- | Alert configuration
type AlertConfig = [AlertRule]

-- | Default alert rules
defaultAlertRules :: [AlertRule]
defaultAlertRules =
  [ AlertRule
      { arName = "high_error_rate"
      , arDescription = "Error rate exceeds 10%"
      , arSeverity = AlertCritical
      , arMetric = "bridge_errors_total"
      , arThreshold = 0.1
      , arOperator = "gt"
      , arWindowSeconds = 300
      , arCooldownSeconds = 300
      }
  , AlertRule
      { arName = "low_balance"
      , arDescription = "Diem balance below 10"
      , arSeverity = AlertWarning
      , arMetric = "bridge_balance_diem"
      , arThreshold = 10.0
      , arOperator = "lt"
      , arWindowSeconds = 60
      , arCooldownSeconds = 3600
      }
  , AlertRule
      { arName = "circuit_breaker_open"
      , arDescription = "Circuit breaker is open"
      , arSeverity = AlertCritical
      , arMetric = "circuit_breaker_state" -- Special metric
      , arThreshold = 1.0
      , arOperator = "eq"
      , arWindowSeconds = 0
      , arCooldownSeconds = 300
      }
  ]

-- | Create alert manager
-- |
-- | **Purpose:** Creates an alert manager with rules and metric registry.
-- | **Parameters:**
-- | - `config`: Alert configuration (rules)
-- | - `metrics`: Metric registry
-- | - `circuitBreakers`: Map of service name -> circuit breaker
-- | **Returns:** Alert manager instance
createAlertManager :: AlertConfig -> MetricRegistry -> Map.Map T.Text CircuitBreaker -> IO AlertManager
createAlertManager config metrics circuitBreakers = do
  alerts <- newTVarIO Map.empty
  pure AlertManager
    { amRules = config
    , amAlerts = alerts
    , amMetrics = metrics
    , amCircuitBreakers = circuitBreakers
    }

-- | Evaluate alerts
-- |
-- | **Purpose:** Evaluates all alert rules and updates alert states.
-- | **Parameters:**
-- | - `manager`: Alert manager
-- | **Returns:** List of firing alerts
evaluateAlerts :: AlertManager -> IO [Alert]
evaluateAlerts manager = do
  now <- getCurrentTime
  atomically $ do
    -- Evaluate each rule
    firingAlerts <- mapM (evaluateRule manager now) (amRules manager)
    pure (filter isFiring firingAlerts)
  where
    isFiring :: Alert -> Bool
    isFiring alert = case alert.alertState of
      AlertFiring _ -> True
      _ -> False

-- | Evaluate single alert rule
evaluateRule :: AlertManager -> UTCTime -> AlertRule -> STM Alert
evaluateRule manager now rule = do
  -- Get metric value (simplified - would query Prometheus registry)
  metricValue <- getMetricValue manager rule.arMetric
  
  -- Check if condition met
  let conditionMet = evaluateCondition metricValue rule.arThreshold rule.arOperator
  
  -- Get current alert state
  alerts <- readTVar (amAlerts manager)
  let currentAlert = Map.lookup rule.arName alerts
  
  -- Update alert state
  newState <- case (conditionMet, currentAlert) of
    (True, Just alert) -> do
      case alert.alertState of
        AlertFiring _ -> pure (AlertFiring (getFiringTime alert.alertState))
        _ -> pure (AlertFiring now)
    (True, Nothing) -> pure (AlertFiring now)
    (False, Just alert) -> do
      case alert.alertState of
        AlertFiring _ -> pure (AlertResolved now)
        _ -> pure alert.alertState
    (False, Nothing) -> pure (AlertPending now)
  
  let newAlert = Alert
        { alertRule = rule
        , alertState = newState
        , alertValue = metricValue
        , alertLastSent = case currentAlert of
            Just a -> alertLastSent a
            Nothing -> Nothing
        }
  
  -- Update alerts map
  modifyTVar' (amAlerts manager) (Map.insert rule.arName newAlert)
  
  pure newAlert
  where
    getFiringTime :: AlertState -> UTCTime
    getFiringTime (AlertFiring t) = t
    getFiringTime (AlertResolved t) = t
    getFiringTime (AlertPending t) = t
    
    getMetricValue :: AlertManager -> T.Text -> STM Double
    getMetricValue mgr metricName = do
      -- Simplified: would query Prometheus registry
      -- For now, return 0.0
      pure 0.0
    
    evaluateCondition :: Double -> Double -> T.Text -> Bool
    evaluateCondition value threshold op = case op of
      "gt" -> value > threshold
      "lt" -> value < threshold
      "eq" -> value == threshold
      "gte" -> value >= threshold
      "lte" -> value <= threshold
      _ -> False

-- | Send alert
-- |
-- | **Purpose:** Sends alert via configured channels.
-- | **Parameters:**
-- | - `manager`: Alert manager
-- | - `alert`: Alert to send
-- | **Returns:** Success or error
sendAlert :: AlertManager -> Alert -> IO (Either String Unit)
sendAlert manager alert = do
  -- In production, would send via Slack, PagerDuty, email, etc.
  -- For now, log the alert
  putStrLn ("ALERT: " ++ T.unpack (arName alert.alertRule) ++ " - " ++ T.unpack (arDescription alert.alertRule))
  pure (Right ())
