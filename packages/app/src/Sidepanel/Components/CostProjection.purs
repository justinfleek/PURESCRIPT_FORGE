-- | Cost Projection Component - Forecasting and Budget Management Widget
-- |
-- | **What:** Displays cost projection widget showing when balance will deplete, usage
-- |         scenarios (light/current/heavy), and recommendations. Provides visual chart
-- |         of projected balance over time.
-- | **Why:** Helps users understand when they'll run out of Diem, plan usage, and make
-- |         informed decisions about model selection and usage patterns.
-- | **How:** Calculates depletion predictions from current balance and consumption rate,
-- |         generates scenarios, and renders chart with projection data.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.Projection`: Projection algorithms and types
-- | - `Sidepanel.State.Balance`: BalanceState for current balance and rate
-- | - `Sidepanel.FFI.DateTime`: DateTime utilities
-- | - `Sidepanel.FFI.Recharts`: Chart rendering
-- |
-- | **Mathematical Foundation:**
-- | - **Projection:** Uses `calculateTimeToDepletion` to project when balance reaches zero
-- | - **Scenarios:** Generates light (0.5x), current (1.0x), heavy (1.5x) usage scenarios
-- | - **Chart Data:** Projects balance at intervals (every hour) until reset or depletion
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.CostProjection as CostProjection
-- |
-- | -- In parent component:
-- | HH.slot _projection unit CostProjection.component
-- |   { balanceState: appState.balance, resetTime: nextMidnight }
-- |   (const HandleAppAction)
-- | ```
-- |
-- | Based on spec 15-COST-PROJECTION.md
module Sidepanel.Components.CostProjection where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Effect.Aff (delay, Milliseconds(..))
import Data.Array as Array
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Data.Int as Int
import Data.DateTime (DateTime(..))
import Data.Date (canonicalDate)
import Data.Time (midnight)
import Data.Date.Component (Year(..), Month(..), Day(..))
import Sidepanel.Projection (DepletionPrediction, Scenario, calculateTimeToDepletion, generateScenarios)
import Sidepanel.State.Balance (BalanceState)
import Sidepanel.Utils.Currency (formatDiem, formatNumber)
import Sidepanel.Utils.Time (formatTime)
import Sidepanel.FFI.DateTime (getCurrentDateTime, toTimestamp, fromTimestamp)

-- | Chart data point for projection chart
type ChartPoint =
  { time :: DateTime
  , projected :: Number
  , isWarningZone :: Boolean
  }

-- | Component input
type Input =
  { balanceState :: BalanceState
  , resetTime :: DateTime  -- UTC midnight reset time
  }

-- | Component state
type State =
  { balanceState :: BalanceState
  , resetTime :: DateTime
  , currentTime :: DateTime
  , prediction :: DepletionPrediction
  , scenarios :: Array Scenario
  , chartData :: Array ChartPoint
  }

-- | Actions
data Action
  = Receive Input
  | Initialize
  | UpdateCurrentTime DateTime
  | Tick  -- Update every second

-- | Outputs
data Output
  = ProjectionUpdated DepletionPrediction

-- | Component
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \input ->
      let
        currentTime = input.balanceState.lastUpdated # fromMaybe (DateTime (canonicalDate (Year 2026) (Month 1) (Day 1)) midnight)
        currentDiem = input.balanceState.venice.diem # fromMaybe 0.0
        consumptionRate = input.balanceState.consumptionRate
        prediction = calculateTimeToDepletion currentDiem consumptionRate input.resetTime currentTime
        scenarios = generateScenarios currentDiem consumptionRate input.resetTime currentTime
        chartData = generateChartData currentDiem consumptionRate input.resetTime currentTime
      in
        { balanceState: input.balanceState
        , resetTime: input.resetTime
        , currentTime
        , prediction
        , scenarios
        , chartData
        }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      , initialize = Just Initialize
      }
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "cost-projection-widget") ]
    [ renderHeader state
    , renderChart state.chartData
    , renderScenarios state.scenarios
    , renderRecommendation state.prediction
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.header
    [ HP.class_ (H.ClassName "projection-widget__header") ]
    [ HH.h3_ [ HH.text "Projected Usage" ]
    , HH.button
        [ HP.class_ (H.ClassName "btn btn--ghost")
        , HP.title "Settings"
        ]
        [ HH.text "⚙" ]
    ]

renderChart :: forall m. Array ChartPoint -> H.ComponentHTML Action () m
renderChart points =
  HH.div
    [ HP.class_ (H.ClassName "projection-chart") ]
    [ HH.div
        [ HP.class_ (H.ClassName "chart-placeholder") ]
        [ HH.text "Chart visualization (would use Recharts)" ]
    , HH.div
        [ HP.class_ (H.ClassName "chart-data") ]
        (Array.map renderChartPoint points)
    ]

renderChartPoint :: forall m. ChartPoint -> H.ComponentHTML Action () m
renderChartPoint point =
  HH.div
    [ HP.class_ (H.ClassName $ "chart-point" <> if point.isWarningZone then " chart-point--warning" else "") ]
    [ HH.text $ formatTime point.time <> ": " <> formatDiem point.projected ]

renderScenarios :: forall m. Array Scenario -> H.ComponentHTML Action () m
renderScenarios scenarios =
  HH.div
    [ HP.class_ (H.ClassName "projection-scenarios") ]
    [ HH.h4 [ HP.class_ (H.ClassName "scenarios-title") ] [ HH.text "Scenarios" ]
    , HH.div
        [ HP.class_ (H.ClassName "scenarios-list") ]
        (Array.map renderScenario scenarios)
    ]

renderScenario :: forall m. Scenario -> H.ComponentHTML Action () m
renderScenario scenario =
  HH.div
    [ HP.class_ (H.ClassName "scenario") ]
    [ HH.span
        [ HP.class_ (H.ClassName "scenario-name") ]
        [ HH.text $ scenario.name <> " (" <> formatRate scenario.rate <> "/hr):" ]
    , HH.span
        [ HP.class_ (H.ClassName "scenario-prediction") ]
        [ HH.text $ formatPrediction scenario.prediction ]
    ]

renderRecommendation :: forall m. DepletionPrediction -> H.ComponentHTML Action () m
renderRecommendation prediction =
  let
    Tuple icon message = getRecommendation prediction
  in
    HH.div
      [ HP.class_ (H.ClassName "projection-recommendation") ]
      [ HH.span
          [ HP.class_ (H.ClassName "recommendation-icon") ]
          [ HH.text icon ]
      , HH.span
          [ HP.class_ (H.ClassName "recommendation-text") ]
          [ HH.text message ]
      ]

formatRate :: Number -> String
formatRate rate = formatDiem rate <> "/hr"

formatPrediction :: DepletionPrediction -> String
formatPrediction prediction
  | not prediction.willDeplete = "Runs out at: Never (balance stable)"
  | prediction.willMakeItToReset = 
      "Makes it to reset with " <> formatDiem prediction.balanceAtReset <> " Diem left"
  | otherwise = case prediction.depletionTime of
      Just dt -> "Runs out at: " <> formatTime dt <> " (" <> formatHours prediction.hoursRemaining <> ")"
      Nothing -> "Runs out: Unknown"

formatHours :: Number -> String
formatHours hours =
  let
    h = round hours
    m = round ((hours - Int.toNumber h) * 60.0)
  in
    if h > 0 then
      show h <> "h " <> show m <> "m"
    else
      show m <> "m"

getRecommendation :: DepletionPrediction -> Tuple String String
getRecommendation prediction
  | not prediction.willDeplete =
      Tuple "✓" "You're using credits very slowly. Balance will last well beyond reset."
  | prediction.willMakeItToReset =
      Tuple "💡" $ "At your current pace, you'll have " <> 
                   formatDiem prediction.balanceAtReset <> " Diem left at reset."
  | prediction.hoursRemaining < 1.0 =
      Tuple "⚠" "Warning: You'll run out in less than an hour. Consider slowing down."
  | otherwise =
      Tuple "💡" $ "At your current pace, you'll run out before reset. " <>
                   "Consider using smaller models for simple tasks."

generateChartData :: Number -> Number -> DateTime -> DateTime -> Array ChartPoint
generateChartData currentBalance rate resetTime currentTime =
  let
    hoursToReset = (toTimestamp resetTime - toTimestamp currentTime) / (3600.0 * 1000.0)
    maxHours = if rate > 0.0 then min hoursToReset (currentBalance / rate) else hoursToReset
    intervals = Array.range 0 (round maxHours)
    warningThreshold = 2.0  -- Hours before reset to show warning
  in
    Array.map (\hour ->
      let
        hourNumber = Int.toNumber hour
        projected = max 0.0 (currentBalance - (rate * hourNumber))
        time = fromTimestamp (toTimestamp currentTime + (hourNumber * 3600.0 * 1000.0))
        isWarningZone = (hoursToReset - hourNumber) < warningThreshold
      in
        { time, projected, isWarningZone }
    ) intervals

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Start ticker to update current time every second
    void $ H.fork $ startTicker
  
  Receive input -> do
    currentTime <- liftEffect getCurrentDateTime
    let currentDiem = input.balanceState.venice.diem # fromMaybe 0.0
    let consumptionRate = input.balanceState.consumptionRate
    let prediction = calculateTimeToDepletion currentDiem consumptionRate input.resetTime currentTime
    let scenarios = generateScenarios currentDiem consumptionRate input.resetTime currentTime
    let chartData = generateChartData currentDiem consumptionRate input.resetTime currentTime
    H.modify_ _
      { balanceState = input.balanceState
      , resetTime = input.resetTime
      , currentTime
      , prediction
      , scenarios
      , chartData
      }
    H.raise (ProjectionUpdated prediction)
  
  UpdateCurrentTime dt ->
    H.modify_ _ { currentTime = dt }
  
  Tick -> do
    currentTime <- liftEffect getCurrentDateTime
    state <- H.get
    let currentDiem = state.balanceState.venice.diem # fromMaybe 0.0
    let consumptionRate = state.balanceState.consumptionRate
    let prediction = calculateTimeToDepletion currentDiem consumptionRate state.resetTime currentTime
    let scenarios = generateScenarios currentDiem consumptionRate state.resetTime currentTime
    let chartData = generateChartData currentDiem consumptionRate state.resetTime currentTime
    H.modify_ _
      { currentTime
      , prediction
      , scenarios
      , chartData
      }
    H.raise (ProjectionUpdated prediction)

-- | Start ticker - Update every second
startTicker :: forall m. MonadAff m => H.HalogenM State Action () Output m Unit
startTicker = do
  delay (Milliseconds 1000.0)
  handleAction Tick
  startTicker  -- Recursive
