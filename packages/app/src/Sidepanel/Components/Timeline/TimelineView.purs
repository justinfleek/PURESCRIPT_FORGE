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
import Data.Array.NonEmpty as NEA
import Data.Maybe (Maybe(..), fromMaybe)
import Data.DateTime (DateTime)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Sidepanel.State.AppState (AppState, SessionState, ProofState, SnapshotSummary)
import Sidepanel.State.Balance (BalanceState)
import Sidepanel.Utils.Currency (formatDiem, formatUSD)
import Sidepanel.Utils.Time (formatTime)
import Sidepanel.WebSocket.Client as WS
import Sidepanel.Api.Bridge as Bridge
import Sidepanel.FFI.DateTime (fromISOString, getCurrentDateTime)
import Data.Int (toNumber)
import Data.Int as Data.Int
import Data.String as String
import Data.Either (Either(..))
import Data.Number (abs)
import Math (max, min, floor)
import Web.UIEvent.MouseEvent (MouseEvent, clientX, toEvent)
import Web.Event.Event (currentTarget) as Event
import Web.DOM.Element (fromEventTarget, getBoundingClientRect) as Element
import Effect (Effect)

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
  | HandleScrubStart MouseEvent
  | HandleScrubMove MouseEvent
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
    , HP.ref scrubberRef
    , HE.onMouseDown HandleScrubStart
    , HE.onMouseMove HandleScrubMove
    , HE.onMouseUp \_ -> HandleScrubEnd
    , HE.onMouseLeave \_ -> HandleScrubEnd
    ]
    [ HH.div [ HP.class_ (H.ClassName "scrubber__track") ] []
    , HH.div
        [ HP.class_ (H.ClassName "scrubber__markers") ]
        (Array.mapWithIndex (\index snapshot -> renderMarker state snapshot index) state.snapshots)
    , HH.div
        [ HP.class_ (H.ClassName "scrubber__playhead")
        , HP.style $ "left: " <> show (playheadPosition state) <> "%"
        ]
        []
    , HH.div
        [ HP.class_ (H.ClassName "scrubber__labels") ]
        (renderTimeLabels state.timeRange)
    ]
  where
    scrubberRef = H.RefLabel "scrubber"

renderMarker :: forall m. State -> SnapshotSummary -> Int -> H.ComponentHTML Action () m
renderMarker state snapshot index =
  let
    total = Array.length state.snapshots
    -- Use index-based position for now (can be enhanced with timestamp-based later)
    position = calculatePositionFromIndex index total
    isSelected = state.selectedId == Just snapshot.id
    markerClass = getMarkerClass snapshot isSelected
    markerIcon = getMarkerIcon snapshot
  in
    HH.div
      [ HP.classes [ H.ClassName "scrubber__marker", markerClass ]
      , HP.style $ "left: " <> show position <> "%"
      , HE.onClick \_ -> SelectSnapshot snapshot.id
      , HP.title $ formatSnapshotTooltip snapshot
      ]
      [ HH.text markerIcon ]

-- | Get marker icon based on snapshot type
getMarkerIcon :: SnapshotSummary -> String
getMarkerIcon snapshot =
  -- Note: SnapshotSummary doesn't have isManual/hasWarning/hasError fields yet
  -- This would be enhanced when SnapshotSummary is extended
  "●"

getMarkerClass :: SnapshotSummary -> Boolean -> H.ClassName
getMarkerClass snapshot isSelected =
  H.ClassName $ if isSelected
    then "marker--selected"
    else "marker--auto"

-- | Calculate position of snapshot within timeline based on timestamp
-- | Returns percentage (0-100) based on actual time differences
-- | Note: This is a pure function that calculates position, but requires current time
-- |       For rendering, we'll use a simpler index-based approach or pass current time
calculatePositionFromTime :: DateTime -> DateTime -> TimeRange -> Number
calculatePositionFromTime snapshotTime currentTime range =
  let
    rangeMs = getTimeRangeMs range
    snapshotMs = toTimestamp snapshotTime
    currentMs = toTimestamp currentTime
    startMs = currentMs - rangeMs
    position = ((snapshotMs - startMs) / rangeMs) * 100.0
  in
    max 0.0 (min 100.0 position)

-- | Fallback: Calculate position based on index (for when timestamps aren't available)
calculatePositionFromIndex :: Int -> Int -> Number
calculatePositionFromIndex index total =
  if total > 0 then (toNumber index / toNumber total) * 100.0 else 0.0

-- | Get time range in milliseconds
getTimeRangeMs :: TimeRange -> Number
getTimeRangeMs = case _ of
  LastHour -> 60.0 * 60.0 * 1000.0
  Last6Hours -> 6.0 * 60.0 * 60.0 * 1000.0
  Last24Hours -> 24.0 * 60.0 * 60.0 * 1000.0
  AllTime -> 7.0 * 24.0 * 60.0 * 60.0 * 1000.0  -- 7 days

-- | Convert DateTime to timestamp (milliseconds)
toTimestamp :: DateTime -> Number
toTimestamp dt = toTimestampImpl dt

foreign import toTimestampImpl :: DateTime -> Number

playheadPosition :: State -> Number
playheadPosition state =
  -- Playhead is always at 100% (NOW)
  100.0

formatSnapshotTooltip :: SnapshotSummary -> String
formatSnapshotTooltip snapshot =
  formatTime snapshot.timestamp <> " - " <> snapshot.description

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
  let currentDiem = case current.venice of
        Just v -> v.diem
        Nothing -> 0.0
      diff = snapshot.diem - currentDiem
  in
    HH.div_
      [ HH.div
          [ HP.class_ (H.ClassName "comparison-value") ]
          [ HH.text $ "◉ " <> formatDiem snapshot.diem <> " Diem" ]
      , HH.div
          [ HP.class_ (H.ClassName "comparison-current") ]
          [ HH.text $ "(vs " <> formatDiem currentDiem <> " now)" ]
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

-- | Calculate scrub position as a percentage (0-100) from a mouse event
-- | Uses the event's currentTarget to get the scrubber element's bounding rect
calculateScrubPositionFromEvent :: MouseEvent -> Effect Number
calculateScrubPositionFromEvent event =
  case Event.currentTarget (toEvent event) of
    Just target -> case Element.fromEventTarget target of
      Just element -> do
        rect <- Element.getBoundingClientRect element
        let mouseX = toNumber (clientX event)
        let relativeX = mouseX - rect.left
        let percentage = (relativeX / rect.width) * 100.0
        pure (max 0.0 (min 100.0 percentage))
      Nothing -> pure 0.0
    Nothing -> pure 0.0

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    H.modify_ _ { snapshots = [] }
    handleAction LoadSnapshots

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
                Nothing -> case currentState.balance.venice of
                  Just v -> { diem: v.diem, usd: v.usd, effective: v.effective }
                  Nothing -> { diem: 0.0, usd: 0.0, effective: 0.0 }
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
        { balance: case appState.balance.venice of
            Just v -> { diem: v.diem, usd: v.usd, effective: v.effective }
            Nothing -> { diem: 0.0, usd: 0.0, effective: 0.0 }
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
            handleAction LoadSnapshots
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

  HandleScrubStart event -> do
    H.modify_ _ { isDragging = true }
    handleAction (HandleScrubMove event)

  HandleScrubMove event -> do
    state <- H.get
    if state.isDragging then do
      -- Calculate position from mouse X relative to scrubber element
      position <- liftEffect $ calculateScrubPositionFromEvent event
      -- Calculate which snapshot is closest to the scrub position
      let total = toNumber (Array.length state.snapshots)
      let index = floor ((position / 100.0) * total)
      let clampedIndex = max 0.0 (min index (total - 1.0))
      case Array.index state.snapshots (Data.Int.floor clampedIndex) of
        Just snapshot -> handleAction (SelectSnapshot snapshot.id)
        Nothing -> pure unit
    else
      pure unit

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
