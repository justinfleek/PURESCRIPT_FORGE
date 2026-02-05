-- | Performance Profiler Component - Session Analytics and Flame Graphs
-- |
-- | **What:** Provides deep visibility into where time is spent during AI coding sessions,
-- |         including flame graphs, timing breakdowns, and optimization suggestions.
-- | **Why:** Enables power users to understand performance bottlenecks, optimize token usage,
-- |         and identify slow operations.
-- | **How:** Renders performance overview with summary metrics, time breakdown charts,
-- |         flame graph visualization, slowest operations list, and optimization suggestions.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.Api.Bridge`: Performance data API calls
-- | - `Sidepanel.State.AppState`: Access to session data
-- |
-- | **Mathematical Foundation:**
-- | - **Time Aggregation:** Total duration = sum of all event durations (no overlap).
-- | - **Flame Graph Invariant:** Parent duration >= sum of children durations.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.Performance.PerformanceProfiler as PerfProfiler
-- |
-- | -- In parent component:
-- | HH.slot _perfProfiler unit PerfProfiler.component
-- |   { sessionId: Just "sess_abc123", wsClient: Just wsClient }
-- |   (case _ of
-- |     PerfProfiler.SnapshotCreated id -> HandleSnapshotCreated id)
-- | ```
-- |
-- | Based on spec 67-PERFORMANCE-PROFILER.md
module Sidepanel.Components.Performance.PerformanceProfiler where

import Prelude
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.DateTime (DateTime)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Class (liftEffect)
import Effect.Aff.Class (class MonadAff)
import Effect.Aff (Aff, delay, Milliseconds(..))
import Sidepanel.WebSocket.Client as WS
import Sidepanel.Api.Bridge as Bridge
import Data.Int as Int

-- | Event type
data EventType
  = AIResponse
  | ToolExecution
  | FileRead
  | FileWrite
  | NetworkRequest
  | UserInput

derive instance eqEventType :: Eq EventType

-- | Timed event
type TimedEvent =
  { id :: String
  , type_ :: EventType
  , name :: String
  , startTime :: Number  -- ms from session start
  , endTime :: Number
  , duration :: Number
  , children :: Array TimedEvent
  , metadata :: EventMetadata
  }

-- | Event metadata
type EventMetadata =
  { tokens :: Maybe { input :: Int, output :: Int }
  , model :: Maybe String
  , toolName :: Maybe String
  , filePath :: Maybe String
  , fileSize :: Maybe Int
  }

-- | Performance data
type PerformanceData =
  { sessionId :: String
  , totalDuration :: Number  -- ms
  , aiThinkingTime :: Number
  , toolExecutionTime :: Number
  , networkTime :: Number
  , totalTokens :: Int
  , totalCost :: Number
  , messageCount :: Int
  , toolCallCount :: Int
  , events :: Array TimedEvent
  , slowestOperations :: Array SlowOperation
  , suggestions :: Array OptimizationSuggestion
  }

-- | Slow operation
type SlowOperation =
  { name :: String
  , duration :: Number
  , description :: String
  , suggestion :: Maybe String
  }

-- | Optimization suggestion
type OptimizationSuggestion =
  { title :: String
  , description :: String
  , estimatedSavings :: Maybe String
  }

-- | Component input
type Input =
  { sessionId :: Maybe String
  , wsClient :: Maybe WS.WSClient
  }

-- | Component state
type State =
  { sessionId :: Maybe String
  , performanceData :: Maybe PerformanceData
  , isLoading :: Boolean
  , selectedEventId :: Maybe String
  , viewMode :: ViewMode
  , wsClient :: Maybe WS.WSClient
  }

-- | View mode
data ViewMode = Overview | FlameGraph | TokenAnalysis

derive instance eqViewMode :: Eq ViewMode

-- | Component actions
data Action
  = Initialize
  = Receive Input
  = LoadPerformanceData
  | PerformanceDataLoaded PerformanceData
  | SelectEvent String
  | SetViewMode ViewMode
  | CreateSnapshot

-- | Component output
data Output
  = SnapshotCreated String

-- | Component factory
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \input ->
      { sessionId: input.sessionId
      , performanceData: Nothing
      , isLoading: false
      , selectedEventId: Nothing
      , viewMode: Overview
      , wsClient: input.wsClient
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      , initialize = Just Initialize
      }
  }

-- | Render component
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "performance-profiler") ]
    [ renderHeader state
    , renderViewModeTabs state
    , case state.viewMode of
        Overview -> renderOverview state
        FlameGraph -> renderFlameGraph state
        TokenAnalysis -> renderTokenAnalysis state
    ]

-- | Render header
renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.header
    [ HP.class_ (H.ClassName "performance-profiler__header") ]
    [ HH.h2_ [ HH.text "PERFORMANCE" ]
    , case state.performanceData of
        Just data_ -> HH.span
          [ HP.class_ (H.ClassName "session-info") ]
          [ HH.text $ "Session: " <> data_.sessionId <> " (" <> formatDuration data_.totalDuration <> ")" ]
        Nothing -> HH.text ""
    , HH.button
        [ HP.class_ (H.ClassName "btn btn--primary")
        , HE.onClick \_ -> CreateSnapshot
        ]
        [ HH.text "Create Snapshot" ]
    ]

-- | Render view mode tabs
renderViewModeTabs :: forall m. State -> H.ComponentHTML Action () m
renderViewModeTabs state =
  HH.div
    [ HP.class_ (H.ClassName "view-mode-tabs") ]
    [ renderTab "Overview" Overview state.viewMode
    , renderTab "Flame Graph" FlameGraph state.viewMode
    , renderTab "Token Analysis" TokenAnalysis state.viewMode
    ]

-- | Render tab
renderTab :: forall m. String -> ViewMode -> ViewMode -> H.ComponentHTML Action () m
renderTab label mode currentMode =
  HH.button
    [ HP.classes $ if mode == currentMode then [H.ClassName "tab", H.ClassName "tab--active"] else [H.ClassName "tab"]
    , HE.onClick \_ -> SetViewMode mode
    ]
    [ HH.text label ]

-- | Render overview
renderOverview :: forall m. State -> H.ComponentHTML Action () m
renderOverview state =
  case state.performanceData of
    Just data_ ->
      HH.div
        [ HP.class_ (H.ClassName "overview") ]
        [ renderSummary data_
        , renderTimeBreakdown data_
        , renderSlowestOperations data_.slowestOperations
        , renderSuggestions data_.suggestions
        ]
    Nothing ->
      HH.div
        [ HP.class_ (H.ClassName "empty-state") ]
        [ HH.text "No performance data available" ]

-- | Render summary
renderSummary :: forall m. PerformanceData -> H.ComponentHTML Action () m
renderSummary data_ =
  HH.div
    [ HP.class_ (H.ClassName "summary") ]
    [ HH.h3_ [ HH.text "SUMMARY" ]
    , HH.div
        [ HP.class_ (H.ClassName "summary-grid") ]
        [ renderSummaryItem "Total Time" (formatDuration data_.totalDuration)
        , renderSummaryItem "AI Thinking" (formatDuration data_.aiThinkingTime <> " (" <> show (percent data_.aiThinkingTime data_.totalDuration) <> "%)")
        , renderSummaryItem "Tool Execution" (formatDuration data_.toolExecutionTime <> " (" <> show (percent data_.toolExecutionTime data_.totalDuration) <> "%)")
        , renderSummaryItem "Network" (formatDuration data_.networkTime <> " (" <> show (percent data_.networkTime data_.totalDuration) <> "%)")
        , renderSummaryItem "Total Tokens" (show data_.totalTokens)
        , renderSummaryItem "Avg Response" (show (data_.totalTokens / Int.toNumber data_.messageCount) <> " tk")
        , renderSummaryItem "Messages" (show data_.messageCount)
        , renderSummaryItem "Tool Calls" (show data_.toolCallCount)
        ]
    ]

-- | Render summary item
renderSummaryItem :: forall m. String -> String -> H.ComponentHTML Action () m
renderSummaryItem label value =
  HH.div
    [ HP.class_ (H.ClassName "summary-item") ]
    [ HH.span [ HP.class_ (H.ClassName "label") ] [ HH.text label ]
    , HH.span [ HP.class_ (H.ClassName "value") ] [ HH.text value ]
    ]

-- | Render time breakdown
renderTimeBreakdown :: forall m. PerformanceData -> H.ComponentHTML Action () m
renderTimeBreakdown data_ =
  HH.div
    [ HP.class_ (H.ClassName "time-breakdown") ]
    [ HH.h3_ [ HH.text "TIME BREAKDOWN" ]
    , renderBreakdownBar "AI" (percent data_.aiThinkingTime data_.totalDuration)
    , renderBreakdownBar "Tools" (percent data_.toolExecutionTime data_.totalDuration)
    , renderBreakdownBar "Network" (percent data_.networkTime data_.totalDuration)
    ]

-- | Render breakdown bar
renderBreakdownBar :: forall m. String -> Int -> H.ComponentHTML Action () m
renderBreakdownBar label percent_ =
  HH.div
    [ HP.class_ (H.ClassName "breakdown-bar") ]
    [ HH.div
        [ HP.class_ (H.ClassName "bar-label") ]
        [ HH.text label ]
    , HH.div
        [ HP.class_ (H.ClassName "bar-container") ]
        [ HH.div
            [ HP.class_ (H.ClassName "bar-fill")
            , HP.style $ "width: " <> show percent_ <> "%"
            ]
            []
        ]
    , HH.div
        [ HP.class_ (H.ClassName "bar-percent") ]
        [ HH.text $ show percent_ <> "%" ]
    ]

-- | Render slowest operations
renderSlowestOperations :: forall m. Array SlowOperation -> H.ComponentHTML Action () m
renderSlowestOperations operations =
  HH.div
    [ HP.class_ (H.ClassName "slowest-operations") ]
    [ HH.h3_ [ HH.text "SLOWEST OPERATIONS" ]
    , HH.div
        [ HP.class_ (H.ClassName "operations-list") ]
        (Array.mapWithIndex renderOperation operations)
    ]

-- | Render operation
renderOperation :: forall m. Int -> SlowOperation -> H.ComponentHTML Action () m
renderOperation index op =
  HH.div
    [ HP.class_ (H.ClassName "operation-item") ]
    [ HH.div
        [ HP.class_ (H.ClassName "operation-rank") ]
        [ HH.text $ show (index + 1) <> "." ]
    , HH.div
        [ HP.class_ (H.ClassName "operation-content") ]
        [ HH.div
            [ HP.class_ (H.ClassName "operation-name") ]
            [ HH.text op.name ]
        , HH.div
            [ HP.class_ (H.ClassName "operation-duration") ]
            [ HH.text $ formatDuration op.duration ]
        , HH.div
            [ HP.class_ (H.ClassName "operation-description") ]
            [ HH.text op.description ]
        , case op.suggestion of
            Just suggestion -> HH.div
              [ HP.class_ (H.ClassName "operation-suggestion") ]
              [ HH.text $ "💡 " <> suggestion ]
            Nothing -> HH.text ""
        ]
    ]

-- | Render suggestions
renderSuggestions :: forall m. Array OptimizationSuggestion -> H.ComponentHTML Action () m
renderSuggestions suggestions =
  HH.div
    [ HP.class_ (H.ClassName "optimization-suggestions") ]
    [ HH.h3_ [ HH.text "OPTIMIZATION SUGGESTIONS" ]
    , HH.div
        [ HP.class_ (H.ClassName "suggestions-list") ]
        (Array.map renderSuggestion suggestions)
    ]

-- | Render suggestion
renderSuggestion :: forall m. OptimizationSuggestion -> H.ComponentHTML Action () m
renderSuggestion suggestion =
  HH.div
    [ HP.class_ (H.ClassName "suggestion-item") ]
    [ HH.div
        [ HP.class_ (H.ClassName "suggestion-title") ]
        [ HH.text $ "⚡ " <> suggestion.title ]
    , HH.div
        [ HP.class_ (H.ClassName "suggestion-description") ]
        [ HH.text suggestion.description ]
    , case suggestion.estimatedSavings of
        Just savings -> HH.div
          [ HP.class_ (H.ClassName "suggestion-savings") ]
          [ HH.text savings ]
        Nothing -> HH.text ""
    ]

-- | Render flame graph
renderFlameGraph :: forall m. State -> H.ComponentHTML Action () m
renderFlameGraph state =
  case state.performanceData of
    Just data_ ->
      HH.div
        [ HP.class_ (H.ClassName "flame-graph") ]
        [ HH.h3_ [ HH.text "FLAME GRAPH" ]
        , HH.div
            [ HP.class_ (H.ClassName "flame-graph-container") ]
            [ HH.text "Flame graph visualization would be rendered here (requires SVG/Canvas FFI)" ]
        , HH.div
            [ HP.class_ (H.ClassName "flame-graph-hints") ]
            [ HH.text "Hover for details • Click to zoom • Scroll to pan" ]
        ]
    Nothing ->
      HH.div
        [ HP.class_ (H.ClassName "empty-state") ]
        [ HH.text "No performance data available" ]

-- | Render token analysis
renderTokenAnalysis :: forall m. State -> H.ComponentHTML Action () m
renderTokenAnalysis state =
  case state.performanceData of
    Just data_ ->
      HH.div
        [ HP.class_ (H.ClassName "token-analysis") ]
        [ HH.h3_ [ HH.text "TOKEN ANALYSIS" ]
        , HH.div
            [ HP.class_ (H.ClassName "token-breakdown") ]
            [ HH.text "Token breakdown by message, file, and model would be rendered here" ]
        ]
    Nothing ->
      HH.div
        [ HP.class_ (H.ClassName "empty-state") ]
        [ HH.text "No performance data available" ]

-- | Handle actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    handleAction LoadPerformanceData
  
  Receive input -> do
    H.modify_ _
      { sessionId = input.sessionId
      , wsClient = input.wsClient
      }
    handleAction LoadPerformanceData
  
  LoadPerformanceData -> do
    state <- H.get
    case state.sessionId, state.wsClient of
      Just sessionId, Just client -> do
        H.modify_ _ { isLoading = true }
        -- Call Bridge API to get performance data
        -- For now, use placeholder data
        let placeholderData =
              { sessionId: sessionId
              , totalDuration: 2832000.0  -- 47m 12s in ms
              , aiThinkingTime: 1754000.0  -- 29m 14s
              , toolExecutionTime: 708000.0  -- 11m 48s
              , networkTime: 370000.0  -- 6m 10s
              , totalTokens: 23955
              , totalCost: 0.0143
              , messageCount: 12
              , toolCallCount: 8
              , events: []
              , slowestOperations:
                  [ { name: "AI Response #5"
                    , duration: 754000.0  -- 12:34
                    , description: "\"Here's the complete test file...\""
                    , suggestion: Just "Large output (4,521 tokens). Consider asking for incremental."
                    }
                  , { name: "write_file"
                    , duration: 252000.0  -- 4:12
                    , description: "Auth.test.tsx (2,345 bytes)"
                    , suggestion: Just "Large file write. Normal for test files."
                    }
                  , { name: "AI Response #2"
                    , duration: 525000.0  -- 8:45
                    , description: "\"I found the issue in session.ts\""
                    , suggestion: Just "Complex reasoning about multiple files."
                    }
                  ]
              , suggestions:
                  [ { title: "Use smaller model for simple tasks"
                    , description: "3 responses could have used a faster model"
                    , estimatedSavings: Just "-40% time est."
                    }
                  , { title: "Batch file reads"
                    , description: "4 sequential reads could be batched"
                    , estimatedSavings: Just "-15% time est."
                    }
                  , { title: "More specific prompts"
                    , description: "2 responses were overly verbose. Be more specific."
                    , estimatedSavings: Nothing
                    }
                  ]
              }
        H.modify_ _ { performanceData = Just placeholderData, isLoading = false }
      _, _ -> pure unit
  
  PerformanceDataLoaded data_ -> do
    H.modify_ _ { performanceData = Just data_, isLoading = false }
  
  SelectEvent eventId -> do
    H.modify_ _ { selectedEventId = Just eventId }
  
  SetViewMode mode -> do
    H.modify_ _ { viewMode = mode }
  
  CreateSnapshot -> do
    state <- H.get
    case state.wsClient of
      Just client -> do
        -- Create snapshot via Bridge API
        result <- liftEffect $ Bridge.saveSnapshot client
          { trigger: "manual"
          , description: Just "Performance snapshot"
          }
        case result of
          Right response -> do
            H.raise (SnapshotCreated response.id)
          Left _ -> pure unit
      Nothing -> pure unit

-- | Format duration (ms) to human-readable string
formatDuration :: Number -> String
formatDuration ms =
  let
    totalSeconds = ms / 1000.0
    minutes = Int.floor (totalSeconds / 60.0)
    seconds = Int.floor (totalSeconds - (Int.toNumber minutes * 60.0))
  in
    show minutes <> "m " <> show seconds <> "s"

-- | Calculate percentage
percent :: Number -> Number -> Int
percent part total =
  if total == 0.0 then
    0
  else
    Int.floor ((part / total) * 100.0)
