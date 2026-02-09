-- | Token Usage Chart Component - Token Usage Visualization
-- |
-- | **What:** Displays token usage data as a line chart using Recharts, showing prompt
-- |         tokens, completion tokens, total tokens, and cost over time. Supports toggling
-- |         cost display and breakdown visibility.
-- | **Why:** Provides visual representation of token usage trends, helping users understand
-- |         consumption patterns and identify usage spikes.
-- | **How:** Uses FFI to create and update Recharts line chart instances. Renders chart
-- |         container with controls for toggling cost and breakdown display. Limits data
-- |         to 100 points for performance.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.FFI.Recharts`: Recharts FFI bindings
-- |
-- | **Mathematical Foundation:**
-- | - **Data Limiting:** Chart displays maximum 100 data points to maintain performance.
-- |   Older points are discarded when limit is exceeded.
-- | - **Chart Updates:** Chart is updated incrementally when new data arrives, preserving
-- |   existing visualization state.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.TokenUsageChart as TokenChart
-- |
-- | -- In parent component:
-- | HH.slot _chart unit TokenChart.component unit
-- |   (case _ of
-- |     TokenChart.ChartReady -> HandleChartReady
-- |     TokenChart.ChartError msg -> HandleChartError msg)
-- |
-- | -- Update chart data:
-- | H.query _chart unit $ H.tell $ TokenChart.UpdateData dataPoints
-- | ```
-- |
-- | Spec 53: Token Usage Chart with Recharts visualization
module Sidepanel.Components.TokenUsageChart where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Effect.Aff (Aff)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Effect (Effect)
import Data.Array (take, length)
import Data.Maybe (Maybe(..))
import Sidepanel.State.AppState (AppState)
import Sidepanel.State.Balance (BalanceState)
import Sidepanel.FFI.Recharts as Recharts
import Effect.Now (nowMillis)

-- | Token usage data point
type TokenDataPoint =
  { timestamp :: Number
  , promptTokens :: Int
  , completionTokens :: Int
  , totalTokens :: Int
  , cost :: Number
  }

-- | Chart configuration
type ChartConfig =
  { width :: Int
  , height :: Int
  , showCost :: Boolean
  , showBreakdown :: Boolean
  }

-- | Component state
type State =
  { data :: Array TokenDataPoint
  , config :: ChartConfig
  , chart :: Maybe Recharts.ChartInstance
  , elementId :: String
  }

-- | Component actions
data Action
  = Initialize
  | UpdateData (Array TokenDataPoint)
  | ToggleCost
  | ToggleBreakdown

-- | Component output
data Output
  = ChartReady
  | ChartError String

-- | Token Usage Chart component
component :: forall q m. MonadAff m => H.Component q Unit Output m
component =
  H.mkComponent
    { initialState: const initialState
    , render
    , eval: H.mkEval $ H.defaultEval
        { handleAction = handleAction
        , initialize = Just Initialize
        }
    }

initialState :: State
initialState =
  { data: []
  , config:
      { width: 800
      , height: 400
      , showCost: true
      , showBreakdown: true
      }
  , chart: Nothing
  , elementId: "token-usage-chart-default"
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "token-usage-chart") ]
    [ HH.div
        [ HP.class_ (H.ClassName "chart-header") ]
        [ HH.h3_ [ HH.text "Token Usage" ]
        , HH.div
            [ HP.class_ (H.ClassName "chart-controls") ]
            [ HH.button
                [ HP.onClick \_ -> ToggleCost ]
                [ HH.text (if state.config.showCost then "Hide Cost" else "Show Cost") ]
            , HH.button
                [ HP.onClick \_ -> ToggleBreakdown ]
                [ HH.text (if state.config.showBreakdown then "Hide Breakdown" else "Show Breakdown") ]
            ]
        ]
    , HH.div
        [ HP.class_ (H.ClassName "chart-container") ]
        [ renderChart state ]
    ]

renderChart :: forall m. State -> H.ComponentHTML Action () m
renderChart state =
  HH.div
    [ HP.id_ state.elementId
    , HP.class_ (H.ClassName "chart-container")
    ]
    []

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Generate unique element ID
    timestamp <- liftEffect nowMillis
    let elementId = "token-usage-chart-" <> show timestamp
    H.modify_ \s -> s { elementId = elementId }
    -- Initialize chart
    state <- H.get
    chart <- liftEffect $ Recharts.createLineChart state.elementId
      { width: state.config.width
      , height: state.config.height
      , showCost: state.config.showCost
      , showBreakdown: state.config.showBreakdown
      }
      (map toChartDataPoint state.data)
    H.modify_ \s -> s { chart = Just chart }
    H.raise ChartReady
  
  UpdateData data -> do
    let limitedData = take 100 data -- Limit to 100 points
    state <- H.get
    H.modify_ \s -> s { data = limitedData }
    -- Update chart
    case state.chart of
      Just chart -> do
        liftEffect $ Recharts.updateChartData chart (map toChartDataPoint limitedData)
      Nothing ->
        pure unit
  
  ToggleCost -> do
    state <- H.get
    let newConfig = state.config { showCost = not state.config.showCost }
    H.modify_ \s -> s { config = newConfig }
    -- Update chart config
    case state.chart of
      Just chart -> do
        liftEffect $ Recharts.updateChartConfig chart
          { width: newConfig.width
          , height: newConfig.height
          , showCost: newConfig.showCost
          , showBreakdown: newConfig.showBreakdown
          }
      Nothing ->
        pure unit
  
  ToggleBreakdown -> do
    state <- H.get
    let newConfig = state.config { showBreakdown = not state.config.showBreakdown }
    H.modify_ \s -> s { config = newConfig }
    -- Update chart config
    case state.chart of
      Just chart -> do
        liftEffect $ Recharts.updateChartConfig chart
          { width: newConfig.width
          , height: newConfig.height
          , showCost: newConfig.showCost
          , showBreakdown: newConfig.showBreakdown
          }
      Nothing ->
        pure unit

-- | Convert TokenDataPoint to ChartDataPoint
toChartDataPoint :: TokenDataPoint -> Recharts.ChartDataPoint
toChartDataPoint point =
  { timestamp: point.timestamp
  , promptTokens: point.promptTokens
  , completionTokens: point.completionTokens
  , totalTokens: point.totalTokens
  , cost: point.cost
  }
