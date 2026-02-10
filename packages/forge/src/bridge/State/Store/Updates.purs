-- | Bridge State Store Updates
-- | Functions to update individual slices of the application state
module Bridge.State.Store.Updates where

import Prelude
import Effect (Effect)
import Effect.Ref (read, write)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Foldable (traverse_)
import Bridge.State.Store.Types (StateStore, AppState, BalanceState, SessionState, ProofState, UsageMetrics, AlertConfig, AlertLevel)

-- | Partial balance update (all fields optional)
type BalancePartial =
  { diem :: Maybe Number
  , usd :: Maybe Number
  , effective :: Maybe Number
  , lastUpdated :: Maybe (Maybe Number)
  , consumptionRate :: Maybe Number
  , timeToDepletion :: Maybe (Maybe Number)
  , todayUsed :: Maybe Number
  , todayStartBalance :: Maybe Number
  , resetCountdown :: Maybe (Maybe Number)
  , alertLevel :: Maybe AlertLevel
  }

-- | Partial session update (all fields optional except immutable startedAt)
type SessionPartial =
  { promptTokens :: Maybe Int
  , completionTokens :: Maybe Int
  , totalTokens :: Maybe Int
  , cost :: Maybe Number
  , model :: Maybe String
  , provider :: Maybe String
  , messageCount :: Maybe Int
  , updatedAt :: Maybe Number
  }

-- | Partial proof update
type ProofPartial =
  { connected :: Maybe Boolean
  , file :: Maybe (Maybe String)
  , position :: Maybe (Maybe { line :: Int, column :: Int })
  , goals :: Maybe (Array { type_ :: String, context :: Array { name :: String, type_ :: String } })
  , diagnostics :: Maybe (Array { severity :: String, message :: String, range :: { start :: { line :: Int, col :: Int }, end :: { line :: Int, col :: Int } } })
  , suggestedTactics :: Maybe (Array { tactic :: String, confidence :: Number })
  }

-- | Partial metrics update
type MetricsPartial =
  { totalTokens :: Maybe Int
  , totalCost :: Maybe Number
  , averageResponseTime :: Maybe Number
  , toolTimings :: Maybe (Array { tool :: String, duration :: Number })
  }

-- | Update entire balance state
updateBalance :: StateStore -> BalanceState -> Effect Unit
updateBalance store balance = do
  state <- read store.state
  write (state { balance = balance }) store.state
  notifyListeners store "balance" ""

-- | Update balance with partial fields
updateBalancePartial :: StateStore -> BalancePartial -> Effect Unit
updateBalancePartial store partial = do
  state <- read store.state
  let b = state.balance
  let newVenice = b.venice
        { diem = fromMaybe b.venice.diem partial.diem
        , usd = fromMaybe b.venice.usd partial.usd
        , effective = fromMaybe b.venice.effective partial.effective
        }
  let newBalance = b
        { venice = case partial.lastUpdated of
            Just lu -> newVenice { lastUpdated = lu }
            Nothing -> newVenice
        , consumptionRate = fromMaybe b.consumptionRate partial.consumptionRate
        , timeToDepletion = case partial.timeToDepletion of
            Just ttd -> ttd
            Nothing -> b.timeToDepletion
        , todayUsed = fromMaybe b.todayUsed partial.todayUsed
        , todayStartBalance = fromMaybe b.todayStartBalance partial.todayStartBalance
        , resetCountdown = case partial.resetCountdown of
            Just rc -> rc
            Nothing -> b.resetCountdown
        , alertLevel = fromMaybe b.alertLevel partial.alertLevel
        }
  write (state { balance = newBalance }) store.state
  notifyListeners store "balance" ""

-- | Update entire session state
updateSession :: StateStore -> SessionState -> Effect Unit
updateSession store session = do
  state <- read store.state
  write (state { session = Just session }) store.state
  notifyListeners store "session" ""

-- | Update session with partial fields
updateSessionPartial :: StateStore -> SessionPartial -> Effect Unit
updateSessionPartial store partial = do
  state <- read store.state
  case state.session of
    Nothing -> pure unit
    Just s -> do
      let newSession = s
            { promptTokens = fromMaybe s.promptTokens partial.promptTokens
            , completionTokens = fromMaybe s.completionTokens partial.completionTokens
            , totalTokens = fromMaybe s.totalTokens partial.totalTokens
            , cost = fromMaybe s.cost partial.cost
            , model = fromMaybe s.model partial.model
            , provider = fromMaybe s.provider partial.provider
            , messageCount = fromMaybe s.messageCount partial.messageCount
            , updatedAt = fromMaybe s.updatedAt partial.updatedAt
            }
      write (state { session = Just newSession }) store.state
      notifyListeners store "session" ""

-- | Clear session
clearSession :: StateStore -> Effect Unit
clearSession store = do
  state <- read store.state
  write (state { session = Nothing }) store.state
  notifyListeners store "session" ""

-- | Update entire proof state
updateProof :: StateStore -> ProofState -> Effect Unit
updateProof store proof = do
  state <- read store.state
  write (state { proof = proof }) store.state
  notifyListeners store "proof" ""

-- | Update proof with partial fields (simplified — replaces arrays entirely)
updateProofPartial :: StateStore -> ProofPartial -> Effect Unit
updateProofPartial store partial = do
  state <- read store.state
  let p = state.proof
  let newProof = p
        { connected = fromMaybe p.connected partial.connected
        }
  write (state { proof = newProof }) store.state
  notifyListeners store "proof" ""

-- | Update entire metrics
updateMetrics :: StateStore -> UsageMetrics -> Effect Unit
updateMetrics store metrics = do
  state <- read store.state
  write (state { metrics = metrics }) store.state
  notifyListeners store "metrics" ""

-- | Update metrics with partial fields
updateMetricsPartial :: StateStore -> MetricsPartial -> Effect Unit
updateMetricsPartial store partial = do
  state <- read store.state
  let m = state.metrics
  let newMetrics = m
        { totalTokens = fromMaybe m.totalTokens partial.totalTokens
        , totalCost = fromMaybe m.totalCost partial.totalCost
        , averageResponseTime = fromMaybe m.averageResponseTime partial.averageResponseTime
        , toolTimings = fromMaybe m.toolTimings partial.toolTimings
        }
  write (state { metrics = newMetrics }) store.state
  notifyListeners store "metrics" ""

-- | Set connected status
setConnected :: StateStore -> Boolean -> Effect Unit
setConnected store connected = do
  state <- read store.state
  write (state { connected = connected }) store.state
  notifyListeners store "connected" ""

-- | Update alert configuration
updateAlertConfig :: StateStore -> AlertConfig -> Effect Unit
updateAlertConfig store config = do
  state <- read store.state
  write (state { alertConfig = config }) store.state
  notifyListeners store "alertConfig" ""

-- | Notify all registered listeners
notifyListeners :: StateStore -> String -> String -> Effect Unit
notifyListeners store path value = do
  ls <- read store.listeners
  traverse_ (\f -> f path value) ls
