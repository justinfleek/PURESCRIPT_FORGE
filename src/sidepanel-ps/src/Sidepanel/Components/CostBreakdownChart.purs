-- | Cost Breakdown Chart Component - Cost Visualization by Model
-- |
-- | **What:** Displays cost breakdown by model as a pie chart using Recharts, showing
-- |         the distribution of costs across different models used in sessions.
-- | **Why:** Provides visual representation of cost allocation, helping users understand
-- |         which models consume the most budget.
-- | **How:** Uses FFI to create and update Recharts pie chart instances. Renders chart
-- |         container with model labels and cost percentages.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.FFI.Recharts`: Recharts FFI bindings (extended for pie charts)
-- |
-- | **Mathematical Foundation:**
-- | - **Cost Aggregation:** Costs are aggregated by model name from session history.
-- | - **Percentage Calculation:** Each model's percentage is calculated as
-- |   `(modelCost / totalCost) * 100`.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.CostBreakdownChart as CostChart
-- |
-- | -- In parent component:
-- | HH.slot_ _costChart unit CostChart.component
-- |   { breakdown: costByModel }
-- | ```
-- |
-- | Spec 50-DASHBOARD-LAYOUT.md
module Sidepanel.Components.CostBreakdownChart where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Effect.Now (nowMillis)
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Sidepanel.FFI.Recharts as Recharts

-- | Cost breakdown by model
type CostBreakdown =
  { model :: String
  , cost :: Number
  , percentage :: Number
  }

-- | Component input
type Input =
  { breakdown :: Array CostBreakdown
  }

-- | Component state
type State =
  { breakdown :: Array CostBreakdown
  , chart :: Maybe Recharts.ChartInstance
  , elementId :: String
  }

-- | Component query
data Query a = UpdateBreakdown (Array CostBreakdown) a

-- | Component output
data Output
  = ChartReady
  | ChartError String

-- | Cost Breakdown Chart component
component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState: \input ->
      { breakdown: input.breakdown
      , chart: Nothing
      , elementId: "cost-breakdown-chart-default"
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , initialize = Just Initialize
      }
  }

data Action = Initialize

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Generate unique element ID
    timestamp <- liftEffect nowMillis
    let elementId = "cost-breakdown-chart-" <> show timestamp
    H.modify_ \s -> s { elementId = elementId }
    -- Initialize chart
    state <- H.get
    chart <- liftEffect $ Recharts.createPieChart state.elementId
      { width: 400
      , height: 400
      , showLabels: true
      , showPercentages: true
      }
      (Array.mapWithIndex toPieChartDataPoint state.breakdown)
    H.modify_ \s -> s { chart = Just chart }
    H.raise ChartReady

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  UpdateBreakdown breakdown k -> do
    H.modify_ _ { breakdown = breakdown }
    -- Update chart with new breakdown data
    state <- H.get
    case state.chart of
      Just chart -> do
        liftEffect $ Recharts.updatePieChartData chart (Array.mapWithIndex toPieChartDataPoint breakdown)
      Nothing ->
        pure unit
    pure (Just k)

-- | Convert CostBreakdown to PieChartDataPoint
toPieChartDataPoint :: Int -> CostBreakdown -> Recharts.PieChartDataPoint
toPieChartDataPoint index item =
  { label: item.model
  , value: item.cost
  , percentage: item.percentage
  , color: getColorForIndex index
  }

-- | Render cost breakdown chart
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "cost-breakdown-chart") ]
    [ HH.div
        [ HP.class_ (H.ClassName "chart-header") ]
        [ HH.h3_ [ HH.text "Cost Breakdown" ]
        ]
    , HH.div
        [ HP.class_ (H.ClassName "chart-container") ]
        [ renderChart state ]
    , renderLegend state.breakdown
    ]

renderChart :: forall m. State -> H.ComponentHTML Action () m
renderChart state =
  HH.div
    [ HP.id_ state.elementId
    , HP.class_ (H.ClassName "chart-container")
    ]
    []

renderLegend :: forall m. Array CostBreakdown -> H.ComponentHTML Action () m
renderLegend breakdown =
  HH.div
    [ HP.class_ (H.ClassName "chart-legend") ]
    (Array.mapWithIndex renderLegendItem breakdown)

renderLegendItem :: forall m. Int -> CostBreakdown -> H.ComponentHTML Action () m
renderLegendItem index item =
  HH.div
    [ HP.class_ (H.ClassName "legend-item") ]
    [ HH.span
        [ HP.class_ (H.ClassName "legend-color")
        , HP.style $ "background-color: " <> getColorForIndex index
        ]
        []
    , HH.span
        [ HP.class_ (H.ClassName "legend-label") ]
        [ HH.text item.model ]
    , HH.span
        [ HP.class_ (H.ClassName "legend-value") ]
        [ HH.text $ show item.percentage <> "%" ]
    ]

-- | Get color for chart segment by index
getColorForIndex :: Int -> String
getColorForIndex index =
  let colors = [ "#4a90e2", "#7ed321", "#f5a623", "#bd10e0", "#50e3c2", "#b8e986", "#9013fe", "#d0021b" ]
  in Array.index colors (index `mod` Array.length colors) # case _ of
    Just color -> color
    Nothing -> "#cccccc"
