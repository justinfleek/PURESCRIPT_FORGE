-- | Timeline View Component - State Timeline and Snapshot Management
-- |
-- | **What:** Displays a timeline of application state snapshots with a scrubber interface
-- |         for navigating through history. Shows snapshot details and comparison with
-- |         current state. Supports creating manual snapshots and restoring to previous
-- |         states.
-- | **Why:** Enables users to view application state history, compare past states with
-- |         current state, and restore to previous states. Essential for debugging and
-- |         state exploration.
-- | **How:** Renders a timeline scrubber with snapshot markers, displays selected
-- |         snapshot details with comparison cards, and provides restore functionality.
-- |         Loads snapshots from Bridge Server via WebSocket.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.State.AppState`: Application state types
-- | - `Sidepanel.WebSocket.Client`: WebSocket communication
-- | - `Sidepanel.Api.Bridge`: Bridge API methods for snapshot operations
-- | - `Sidepanel.Utils.Currency`: Currency formatting
-- | - `Sidepanel.Utils.Time`: Time formatting
-- |
-- | **Mathematical Foundation:**
-- | - **Timeline Position:** Snapshot positions are calculated based on index and total
-- |   count. Playhead is always at 100% (NOW).
-- | - **State Comparison:** Differences between snapshot state and current state are
-- |   calculated and displayed with visual indicators (positive/negative/neutral).
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.Timeline.TimelineView as TimelineView
-- |
-- | -- In parent component:
-- | HH.slot _timeline unit TimelineView.component
-- |   { snapshots: appState.snapshots
-- |   , currentState: appState
-- |   , wsClient: wsClient
-- |   }
-- |   (case _ of
-- |     TimelineView.SnapshotRestored id -> HandleSnapshotRestored id
-- |     TimelineView.SnapshotCreated id -> HandleSnapshotCreated id)
-- | ```
-- |
-- | Based on spec 63-TIMELINE-VIEW.md
module Sidepanel.Components.Timeline.TimelineView where

import Prelude
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.DateTime (DateTime)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Sidepanel.State.AppState (AppState, BalanceState, SessionState, ProofState, SnapshotSummary)
import Sidepanel.Utils.Currency (formatDiem, formatUSD)
import Sidepanel.Utils.Time (formatTime)
import Sidepanel.WebSocket.Client as WS
import Sidepanel.Api.Bridge as Bridge
import Sidepanel.FFI.DateTime (fromISOString, getCurrentDateTime)
import Data.Int (toNumber)
import Data.String as String

-- | Full snapshot with state data
type Snapshot =
  { id :: String
  , timestamp :: DateTime
  , description :: Maybe String
  , state :: SnapshotState
  }

type SnapshotState =
  { balance :: BalanceSnapshot
  , session :: Maybe SessionSnapshot
  , proof :: ProofSnapshot
  , files :: Array FileContext
  }

type BalanceSnapshot =
  { diem :: Number
  , usd :: Number
  , effective :: Number
  }

type SessionSnapshot =
  { messageCount :: Int
  , promptTokens :: Int
  , completionTokens :: Int
  , cost :: Number
  }

type ProofSnapshot =
  { goalCount :: Int
  , diagnosticCount :: Int
  , hasErrors :: Boolean
  }

type FileContext =
  { path :: String
  , lineCount :: Int
  }

-- | Component state
type State =
  { snapshots :: Array SnapshotSummary
  , selectedId :: Maybe String
  , selectedSnapshot :: Maybe Snapshot
  , currentState :: AppState
  , isDragging :: Boolean
  , timeRange :: TimeRange
  , wsClient :: Maybe WS.WSClient
  }

data TimeRange = LastHour | Last6Hours | Last24Hours | AllTime

derive instance eqTimeRange :: Eq TimeRange

-- | Actions
data Action
  = Initialize
  | LoadSnapshots
  | SelectSnapshot String
  | SnapshotLoaded Snapshot
  | CreateManualSnapshot String
  | RestoreSnapshot String
  | SetTimeRange TimeRange
  | HandleScrubStart
  | HandleScrubMove Number
  | HandleScrubEnd
  | ViewDiff

-- | Outputs
data Output
  = SnapshotRestored String
  | SnapshotCreated String

-- | Component input
type Input =
  { snapshots :: Array SnapshotSummary
  , currentState :: AppState
  , wsClient :: Maybe WS.WSClient
  }

-- | Component
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \input ->
      { snapshots: input.snapshots
      , selectedId: Nothing
      , selectedSnapshot: Nothing
      , currentState: input.currentState
      , isDragging: false
      , timeRange: Last24Hours
      , wsClient: input.wsClient
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "timeline-view") ]
    [ renderHeader state
    , renderScrubber state
    , case state.selectedSnapshot of
        Just snapshot -> renderSnapshotDetails snapshot state.currentState
        Nothing -> renderEmptyDetails
    ]

renderHeader :: forall m. State -> H.ComponentHTML Action () m
renderHeader state =
  HH.header
    [ HP.class_ (H.ClassName "timeline-view__header") ]
    [ HH.h2_ [ HH.text "Timeline" ]
    , HH.button
        [ HP.classes [ H.ClassName "btn", H.ClassName "btn--primary" ]
        , HE.onClick \_ -> CreateManualSnapshot ""
        ]
        [ HH.text "Create Snapshot" ]
    ]

renderScrubber :: forall m. State -> H.ComponentHTML Action () m
renderScrubber state =
  HH.div
    [ HP.class_ (H.ClassName "timeline-scrubber")
    , HE.onMouseDown \_ -> HandleScrubStart
    , HE.onMouseUp \_ -> HandleScrubEnd
    , HE.onMouseLeave \_ -> HandleScrubEnd
    ]
    [ HH.div [ HP.class_ (H.ClassName "scrubber__track") ] []
    , HH.div
        [ HP.class_ (H.ClassName "scrubber__markers") ]
        (mapWithIndex (\index snapshot -> renderMarker state snapshot index) state.snapshots)
    , HH.div
        [ HP.class_ (H.ClassName "scrubber__playhead")
        , HP.style $ "left: " <> show (playheadPosition state) <> "%"
        ]
        []
    , HH.div
        [ HP.class_ (H.ClassName "scrubber__labels") ]
        (renderTimeLabels state.timeRange)
    ]

renderMarker :: forall m. State -> SnapshotSummary -> Int -> H.ComponentHTML Action () m
renderMarker state snapshot index =
  let
    total = Array.length state.snapshots
    position = calculatePosition index total
    isSelected = state.selectedId == Just snapshot.id
    markerClass = getMarkerClass snapshot isSelected
  in
    HH.div
      [ HP.classes [ H.ClassName "scrubber__marker", markerClass ]
      , HP.style $ "left: " <> show position <> "%"
      , HE.onClick \_ -> SelectSnapshot snapshot.id
      , HP.title $ formatSnapshotTooltip snapshot
      ]
      []

getMarkerClass :: SnapshotSummary -> Boolean -> H.ClassName
getMarkerClass snapshot isSelected =
  H.ClassName $ if isSelected
    then "marker--selected"
    else "marker--auto"

-- | Calculate position of snapshot within timeline
-- | Returns percentage (0-100) based on snapshot index
-- | Note: Simplified implementation - would calculate based on actual time differences
calculatePosition :: Int -> Int -> Number
calculatePosition index total =
  if total > 0 then (toNumber index / toNumber total) * 100.0 else 0.0

playheadPosition :: State -> Number
playheadPosition state =
  -- Playhead is always at 100% (NOW)
  100.0

formatSnapshotTooltip :: SnapshotSummary -> String
formatSnapshotTooltip snapshot =
  formatTime (fromISOString snapshot.timestamp) <> " - " <> fromMaybe "No description" snapshot.description

renderTimeLabels :: forall m. TimeRange -> Array (H.ComponentHTML Action () m)
renderTimeLabels range =
  case range of
    LastHour -> [ HH.span_ [ HH.text "1h ago" ], HH.span_ [ HH.text "NOW" ] ]
    Last6Hours -> [ HH.span_ [ HH.text "6h ago" ], HH.span_ [ HH.text "3h ago" ], HH.span_ [ HH.text "NOW" ] ]
    Last24Hours -> [ HH.span_ [ HH.text "24h ago" ], HH.span_ [ HH.text "12h ago" ], HH.span_ [ HH.text "NOW" ] ]
    AllTime -> [ HH.span_ [ HH.text "Start" ], HH.span_ [ HH.text "NOW" ] ]

renderSnapshotDetails :: forall m. Snapshot -> AppState -> H.ComponentHTML Action () m
renderSnapshotDetails snapshot current =
  HH.div
    [ HP.class_ (H.ClassName "snapshot-details") ]
    [ HH.div
        [ HP.class_ (H.ClassName "snapshot-details__header") ]
        [ HH.span [ HP.class_ (H.ClassName "section-title") ]
            [ HH.text "Snapshot Details" ]
        , HH.span [ HP.class_ (H.ClassName "snapshot-details__time") ]
            [ HH.text $ formatTime snapshot.timestamp ]
        ]
    , HH.div
        [ HP.class_ (H.ClassName "snapshot-details__cards") ]
        [ renderComparisonCard "Balance"
            (renderBalanceComparison snapshot.state.balance current.balance)
        , renderComparisonCard "Session"
            (renderSessionComparison snapshot.state.session current.session)
        , renderComparisonCard "Context Files"
            (renderFilesComparison snapshot.state.files)
        , renderComparisonCard "Proof State"
            (renderProofComparison snapshot.state.proof current.proof)
        ]
    , HH.div
        [ HP.class_ (H.ClassName "snapshot-details__actions") ]
        [ HH.button
            [ HP.classes [ H.ClassName "btn", H.ClassName "btn--secondary" ]
            , HE.onClick \_ -> ViewDiff
            ]
            [ HH.text "View Diff" ]
        , HH.button
            [ HP.classes [ H.ClassName "btn", H.ClassName "btn--primary" ]
            , HE.onClick \_ -> RestoreSnapshot snapshot.id
            ]
            [ HH.text "Restore to This Point" ]
        ]
    ]

renderEmptyDetails :: forall m. H.ComponentHTML Action () m
renderEmptyDetails =
  HH.div
    [ HP.class_ (H.ClassName "snapshot-details snapshot-details--empty") ]
    [ HH.text "Select a snapshot to view details" ]

renderComparisonCard :: forall m. String -> H.ComponentHTML Action () m -> H.ComponentHTML Action () m
renderComparisonCard title content =
  HH.div
    [ HP.class_ (H.ClassName "comparison-card") ]
    [ HH.div [ HP.class_ (H.ClassName "comparison-card__title") ] [ HH.text title ]
    , content
    ]

renderBalanceComparison :: forall m. BalanceSnapshot -> BalanceState -> H.ComponentHTML Action () m
renderBalanceComparison snapshot current =
  let diff = snapshot.diem - current.diem
  in
    HH.div_
      [ HH.div
          [ HP.class_ (H.ClassName "comparison-value") ]
          [ HH.text $ "◉ " <> formatDiem snapshot.diem <> " Diem" ]
      , HH.div
          [ HP.class_ (H.ClassName "comparison-current") ]
          [ HH.text $ "(vs " <> formatDiem current.diem <> " now)" ]
      , HH.div
          [ HP.classes $ diffClasses diff ]
          [ HH.text $ formatDiff diff ]
      ]

renderSessionComparison :: forall m. Maybe SessionSnapshot -> Maybe SessionState -> H.ComponentHTML Action () m
renderSessionComparison snapshot current = case snapshot, current of
  Just snap, Just curr ->
    HH.div_
      [ HH.div
          [ HP.class_ (H.ClassName "comparison-value") ]
          [ HH.text $ "Messages: " <> show snap.messageCount <> " (vs " <> show curr.messageCount <> " now)" ]
      , HH.div
          [ HP.class_ (H.ClassName "comparison-value") ]
          [ HH.text $ "Tokens: " <> show (snap.promptTokens + snap.completionTokens) <> " (vs " <> show curr.totalTokens <> ")" ]
      ]
  Just snap, Nothing ->
    HH.div_
      [ HH.text $ "Messages: " <> show snap.messageCount ]
  _, _ ->
    HH.text "No session"

renderFilesComparison :: forall m. Array FileContext -> H.ComponentHTML Action () m
renderFilesComparison files =
  HH.div_
    (map (\file -> HH.div_ [ HH.text $ "• " <> file.path ]) files)

renderProofComparison :: forall m. ProofSnapshot -> ProofState -> H.ComponentHTML Action () m
renderProofComparison snapshot current =
  HH.div_
    [ HH.div
        [ HP.class_ (H.ClassName "comparison-value") ]
        [ HH.text $ "Goals: " <> show snapshot.goalCount <> " (vs " <> show (Array.length current.goals) <> " now)" ]
    , HH.div
        [ HP.class_ (H.ClassName "comparison-value") ]
        [ HH.text $ "Diagnostics: " <> show snapshot.diagnosticCount <> " (vs " <> show (Array.length current.diagnostics) <> ")" ]
    ]

diffClasses :: Number -> Array H.ClassName
diffClasses diff
  | diff > 0.0 = [ H.ClassName "diff", H.ClassName "diff--positive" ]
  | diff < 0.0 = [ H.ClassName "diff", H.ClassName "diff--negative" ]
  | otherwise = [ H.ClassName "diff", H.ClassName "diff--neutral" ]

formatDiff :: Number -> String
formatDiff diff
  | diff > 0.0 = "+" <> formatDiem diff <> " higher"
  | diff < 0.0 = formatDiem (abs diff) <> " lower"
  | otherwise = "unchanged"

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    H.modify_ _ { snapshots = [] }
    LoadSnapshots

  LoadSnapshots -> do
    state <- H.get
    case state.wsClient of
      Just client -> do
        result <- H.liftAff $ Bridge.listSnapshots client { limit: Just 100, offset: Nothing }
        case result of
          Right response -> do
            -- Convert SnapshotSummary from Bridge API to AppState SnapshotSummary
            let snapshots = map (\s -> 
                  { id: s.id
                  , timestamp: fromISOString s.timestamp
                  , description: fromMaybe "No description" s.description
                  , stateHash: ""  -- Would be provided by bridge server
                  }
                ) response.snapshots
            H.modify_ _ { snapshots = snapshots }
          Left err -> pure unit  -- Handle error (could show notification)
      Nothing -> pure unit

  SelectSnapshot id -> do
    H.modify_ _ { selectedId = Just id }
    -- Load full snapshot data from bridge server
    state <- H.get
    case state.wsClient of
      Just client -> do
        result <- H.liftAff $ Bridge.getSnapshot client { id: id }
        case result of
          Right response -> do
            -- Convert Bridge response to TimelineView Snapshot
            let snapshot = convertBridgeSnapshotToTimelineSnapshot response state.currentState
            H.modify_ _ { selectedSnapshot = Just snapshot }
          Left err -> pure unit  -- Handle error (could show notification)
      Nothing -> do
        -- Fallback to summary data if no client
        case Array.find (\s -> s.id == id) state.snapshots of
          Just summary -> do
            let snapshot = { id: summary.id, timestamp: summary.timestamp, description: Just summary.description, state: buildSnapshotState state.currentState }
            H.modify_ _ { selectedSnapshot = Just snapshot }
          Nothing -> pure unit
    where
      convertBridgeSnapshotToTimelineSnapshot :: Bridge.SnapshotGetResponse -> AppState -> Snapshot
      convertBridgeSnapshotToTimelineSnapshot response currentState =
        { id: response.id
        , timestamp: fromISOString response.timestamp
        , description: response.description
        , state:
            { balance: case response.state.balance of
                Just bal -> { diem: bal.venice.diem, usd: bal.venice.usd, effective: bal.venice.effective }
                Nothing -> { diem: currentState.balance.diem, usd: currentState.balance.usd, effective: currentState.balance.effective }
            , session: case response.state.session of
                Just sess -> Just { messageCount: sess.messageCount, promptTokens: sess.promptTokens, completionTokens: sess.completionTokens, cost: sess.cost }
                Nothing -> map (\s -> { messageCount: s.messageCount, promptTokens: s.promptTokens, completionTokens: s.completionTokens, cost: s.cost }) currentState.session
            , proof: case response.state.proof of
                Just p -> { goalCount: Array.length p.goals, diagnosticCount: Array.length p.diagnostics, hasErrors: Array.length (Array.filter (\d -> d.severity == "error") p.diagnostics) > 0 }
                Nothing -> { goalCount: Array.length currentState.proof.goals, diagnosticCount: Array.length currentState.proof.diagnostics, hasErrors: Array.length (Array.filter (\d -> d.severity == "error") currentState.proof.diagnostics) > 0 }
            , files: map (\f -> { path: f.path, lineCount: 0 }) response.state.fileContext  -- lineCount would need to be calculated or stored
            }
        }
      
      buildSnapshotState :: AppState -> SnapshotState
      buildSnapshotState appState =
        { balance: { diem: appState.balance.diem, usd: appState.balance.usd, effective: appState.balance.effective }
        , session: map (\s -> { messageCount: s.messageCount, promptTokens: s.promptTokens, completionTokens: s.completionTokens, cost: s.cost }) appState.session
        , proof: { goalCount: Array.length appState.proof.goals, diagnosticCount: Array.length appState.proof.diagnostics, hasErrors: Array.length (Array.filter (\d -> d.severity == "error") appState.proof.diagnostics) > 0 }
        , files: []  -- Fallback: empty if can't load
        }

  SnapshotLoaded snapshot ->
    H.modify_ _ { selectedSnapshot = Just snapshot }

  CreateManualSnapshot description -> do
    state <- H.get
    case state.wsClient of
      Just client -> do
        result <- H.liftAff $ Bridge.saveSnapshot client { trigger: "manual", description: Just description }
        case result of
          Right response -> do
            H.raise (SnapshotCreated response.id)
            -- Reload snapshots
            LoadSnapshots
          Left err -> pure unit  -- Handle error
      Nothing -> pure unit

  RestoreSnapshot id -> do
    state <- H.get
    case state.wsClient of
      Just client -> do
        result <- H.liftAff $ Bridge.restoreSnapshot client { id: id }
        case result of
          Right response -> do
            if response.success then
              H.raise (SnapshotRestored id)
            else
              pure unit
          Left err -> pure unit  -- Handle error
      Nothing -> pure unit

  SetTimeRange range ->
    H.modify_ _ { timeRange = range }

  HandleScrubStart ->
    H.modify_ _ { isDragging = true }

  HandleScrubMove position -> do
    state <- H.get
    -- Calculate which snapshot is closest to the scrub position
    let total = Array.length state.snapshots
    let index = floor ((position / 100.0) * toNumber total)
    let clampedIndex = max 0 (min index (total - 1))
    case Array.index state.snapshots clampedIndex of
      Just snapshot -> SelectSnapshot snapshot.id
      Nothing -> pure unit

  HandleScrubEnd ->
    H.modify_ _ { isDragging = false }

  ViewDiff -> do
    state <- H.get
    case state.selectedSnapshot of
      Just snapshot -> do
        -- Would navigate to diff viewer with snapshot comparison
        -- For now, just log
        pure unit
      Nothing -> pure unit
