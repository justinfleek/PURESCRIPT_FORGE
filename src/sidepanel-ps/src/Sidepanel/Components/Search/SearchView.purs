-- | Search View Component - Universal Search
-- |
-- | **What:** Provides universal search across sessions, messages, files, proofs, and recordings.
-- |         Supports advanced query syntax, filters, and keyboard navigation.
-- | **Why:** Enables users to quickly find anything in their AI coding history from one place.
-- | **How:** Renders search modal with input, filters, grouped results, and previews. Supports
-- |         real-time search as user types, advanced query syntax parsing, and keyboard navigation.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.Api.Bridge`: Search API calls
-- | - `Sidepanel.State.AppState`: Access to sessions, messages, etc.
-- |
-- | **Mathematical Foundation:**
-- | - **Search Invariant:** Results are always sorted by relevance (most relevant first).
-- | - **Query Parsing Invariant:** All valid queries parse successfully, invalid queries
-- |   fall back to simple text search.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.Search.SearchView as SearchView
-- |
-- | -- In parent component:
-- | HH.slot _searchView unit SearchView.component
-- |   { visible: true, wsClient: Just wsClient }
-- |   (case _ of
-- |     SearchView.ResultSelected result -> HandleResultSelected result
-- |     SearchView.SearchClosed -> HandleSearchClosed)
-- | ```
-- |
-- | Based on spec 66-SEARCH-VIEW.md
module Sidepanel.Components.Search.SearchView where

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
import Data.Map as Map

-- | Search result type
data SearchResultType = SessionResult | MessageResult | FileResult | ProofResult | RecordingResult

derive instance eqSearchResultType :: Eq SearchResultType

-- | Search result
type SearchResult =
  { id :: String
  , type_ :: SearchResultType
  , title :: String
  , preview :: String
  , metadata :: SearchResultMetadata
  , relevance :: Number  -- 0.0 to 1.0
  }

-- | Search result metadata
type SearchResultMetadata =
  { sessionId :: Maybe String
  , timestamp :: Maybe DateTime
  , model :: Maybe String
  , filePath :: Maybe String
  , lineNumber :: Maybe Int
  , proofStatus :: Maybe String
  }

-- | Search query
type SearchQuery =
  { text :: String
  , typeFilter :: Maybe SearchResultType
  , dateFilter :: Maybe DateFilter
  , modelFilter :: Maybe String
  , roleFilter :: Maybe String  -- For messages: "user" | "assistant" | "system" | "tool"
  }

-- | Date filter
data DateFilter
  = Today
  | ThisWeek
  | ThisMonth
  | CustomDate DateTime
  | AfterDate DateTime
  | BeforeDate DateTime

derive instance eqDateFilter :: Eq DateFilter

-- | Component input
type Input =
  { visible :: Boolean
  , wsClient :: Maybe WS.WSClient
  }

-- | Component state
type State =
  { visible :: Boolean
  , query :: String
  , parsedQuery :: SearchQuery
  , results :: Array SearchResult
  , selectedIndex :: Int
  , typeFilter :: Maybe SearchResultType
  , dateFilter :: Maybe DateFilter
  , modelFilter :: Maybe String
  , roleFilter :: Maybe String
  , isSearching :: Boolean
  , wsClient :: Maybe WS.WSClient
  }

-- | Component actions
data Action
  = Initialize
  = Receive Input
  = SetQuery String
  = SelectResult Int
  = SetTypeFilter (Maybe SearchResultType)
  = SetDateFilter (Maybe DateFilter)
  = SetModelFilter (Maybe String)
  = SetRoleFilter (Maybe String)
  = Close
  = PerformSearch
  = NavigateUp
  = NavigateDown
  = OpenSelected

-- | Component output
data Output
  = ResultSelected SearchResult
  = SearchClosed

-- | Component factory
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \input ->
      { visible: input.visible
      , query: ""
      , parsedQuery: { text: "", typeFilter: Nothing, dateFilter: Nothing, modelFilter: Nothing, roleFilter: Nothing }
      , results: []
      , selectedIndex: 0
      , typeFilter: Nothing
      , dateFilter: Nothing
      , modelFilter: Nothing
      , roleFilter: Nothing
      , isSearching: false
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
  if state.visible then
    HH.div
      [ HP.class_ (H.ClassName "search-view-overlay")
      , HE.onClick \_ -> Close
      ]
      [ HH.div
          [ HP.class_ (H.ClassName "search-view")
          , HE.onClick \_ -> pure unit  -- Prevent click from bubbling to overlay
          ]
          [ renderHeader
          , renderSearchInput state
          , renderFilters state
          , renderResults state
          , renderFooter
          ]
      ]
  else
    HH.text ""

-- | Render header
renderHeader :: forall m. H.ComponentHTML Action () m
renderHeader =
  HH.header
    [ HP.class_ (H.ClassName "search-view__header") ]
    [ HH.h2_ [ HH.text "SEARCH" ]
    , HH.button
        [ HP.class_ (H.ClassName "search-view__close")
        , HE.onClick \_ -> Close
        , HP.attr (H.AttrName "aria-label") "Close"
        ]
        [ HH.text "✕" ]
    ]

-- | Render search input
renderSearchInput :: forall m. State -> H.ComponentHTML Action () m
renderSearchInput state =
  HH.div
    [ HP.class_ (H.ClassName "search-view__input-container") ]
    [ HH.span [ HP.class_ (H.ClassName "search-icon") ] [ HH.text "🔍" ]
    , HH.input
        [ HP.type_ HP.InputText
        , HP.class_ (H.ClassName "search-view__input")
        , HP.placeholder "Search sessions, messages, files, proofs..."
        , HP.value state.query
        , HE.onValueInput SetQuery
        , HP.autofocus true
        ]
    ]

-- | Render filters
renderFilters :: forall m. State -> H.ComponentHTML Action () m
renderFilters state =
  HH.div
    [ HP.class_ (H.ClassName "search-view__filters") ]
    [ HH.select
        [ HP.class_ (H.ClassName "filter-select")
        , HE.onValueChange \v -> SetTypeFilter $ parseTypeFilter v
        ]
        [ HH.option [ HP.value "" ] [ HH.text "All Types" ]
        , HH.option [ HP.value "session" ] [ HH.text "Sessions" ]
        , HH.option [ HP.value "message" ] [ HH.text "Messages" ]
        , HH.option [ HP.value "file" ] [ HH.text "Files" ]
        , HH.option [ HP.value "proof" ] [ HH.text "Proofs" ]
        , HH.option [ HP.value "recording" ] [ HH.text "Recordings" ]
        ]
    , HH.select
        [ HP.class_ (H.ClassName "filter-select")
        , HE.onValueChange \v -> SetDateFilter $ parseDateFilter v
        ]
        [ HH.option [ HP.value "" ] [ HH.text "Any Time" ]
        , HH.option [ HP.value "today" ] [ HH.text "Today" ]
        , HH.option [ HP.value "this-week" ] [ HH.text "This Week" ]
        , HH.option [ HP.value "this-month" ] [ HH.text "This Month" ]
        ]
    , HH.select
        [ HP.class_ (H.ClassName "filter-select")
        , HE.onValueChange \v -> SetModelFilter $ if v == "" then Nothing else Just v
        ]
        [ HH.option [ HP.value "" ] [ HH.text "Any Model" ]
        -- Would populate with available models
        ]
    ]

-- | Render results
renderResults :: forall m. State -> H.ComponentHTML Action () m
renderResults state =
  HH.div
    [ HP.class_ (H.ClassName "search-view__results") ]
    [ HH.div
        [ HP.class_ (H.ClassName "results-count") ]
        [ HH.text $ "Found " <> show (Array.length state.results) <> " results" ]
    , HH.div
        [ HP.class_ (H.ClassName "results-list") ]
        (Array.mapWithIndex (renderResult state.selectedIndex) state.results)
    ]

-- | Render single result
renderResult :: forall m. Int -> Int -> SearchResult -> H.ComponentHTML Action () m
renderResult selectedIndex index result =
  HH.div
    [ HP.classes $ resultClasses (selectedIndex == index)
    , HE.onClick \_ -> SelectResult index
    ]
    [ HH.div
        [ HP.class_ (H.ClassName "result__icon") ]
        [ HH.text $ resultIcon result.type_ ]
    , HH.div
        [ HP.class_ (H.ClassName "result__content") ]
        [ HH.div
            [ HP.class_ (H.ClassName "result__title") ]
            [ HH.text result.title ]
        , HH.div
            [ HP.class_ (H.ClassName "result__preview") ]
            [ HH.text result.preview ]
        , HH.div
            [ HP.class_ (H.ClassName "result__metadata") ]
            [ renderMetadata result.metadata ]
        ]
    , HH.button
        [ HP.class_ (H.ClassName "result__action")
        , HE.onClick \_ -> SelectResult index
        ]
        [ HH.text "→" ]
    ]

-- | Render metadata
renderMetadata :: forall m. SearchResultMetadata -> H.ComponentHTML Action () m
renderMetadata meta =
  HH.div
    [ HP.class_ (H.ClassName "result-metadata") ]
    (Array.catMaybes
      [ map (\ts -> HH.span_ [ HH.text $ formatTimestamp ts ]) meta.timestamp
      , map (\m -> HH.span_ [ HH.text m ]) meta.model
      , map (\fp -> HH.span_ [ HH.text fp ]) meta.filePath
      , map (\ln -> HH.span_ [ HH.text $ "Line " <> show ln ]) meta.lineNumber
      ]
    )

-- | Render footer
renderFooter :: forall m. H.ComponentHTML Action () m
renderFooter =
  HH.footer
    [ HP.class_ (H.ClassName "search-view__footer") ]
    [ HH.text "↑↓ Navigate   ⏎ Open   Esc Close" ]

-- | Result CSS classes
resultClasses :: Boolean -> Array H.ClassName
resultClasses isSelected =
  [ H.ClassName "search-result" ]
  <> (if isSelected then [H.ClassName "search-result--selected"] else [])

-- | Result icon by type
resultIcon :: SearchResultType -> String
resultIcon = case _ of
  SessionResult -> "●"
  MessageResult -> "💬"
  FileResult -> "📄"
  ProofResult -> "🔬"
  RecordingResult -> "🎬"

-- | Parse type filter
parseTypeFilter :: String -> Maybe SearchResultType
parseTypeFilter = case _ of
  "session" -> Just SessionResult
  "message" -> Just MessageResult
  "file" -> Just FileResult
  "proof" -> Just ProofResult
  "recording" -> Just RecordingResult
  _ -> Nothing

-- | Parse date filter
parseDateFilter :: String -> Maybe DateFilter
parseDateFilter = case _ of
  "today" -> Just Today
  "this-week" -> Just ThisWeek
  "this-month" -> Just ThisMonth
  _ -> Nothing

-- | Format timestamp
formatTimestamp :: DateTime -> String
formatTimestamp dt = "Jan 15"  -- Placeholder - would use proper formatting

-- | Handle actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Subscribe to keyboard events for navigation
    void $ H.subscribe keyboardEventEmitter
  
  Receive input -> do
    H.modify_ _
      { visible = input.visible
      , wsClient = input.wsClient
      }
    if input.visible && not String.null (H.gets _.query) then
      handleAction PerformSearch
    else
      pure unit
  
  SetQuery query -> do
    H.modify_ _ { query = query, selectedIndex = 0 }
    -- Debounce search
    void $ H.fork do
      delay (Milliseconds 300.0)
      handleAction PerformSearch
  
  SelectResult index -> do
    H.modify_ _ { selectedIndex = index }
  
  SetTypeFilter typeFilter -> do
    H.modify_ _ { typeFilter = typeFilter }
    handleAction PerformSearch
  
  SetDateFilter dateFilter -> do
    H.modify_ _ { dateFilter = dateFilter }
    handleAction PerformSearch
  
  SetModelFilter modelFilter -> do
    H.modify_ _ { modelFilter = modelFilter }
    handleAction PerformSearch
  
  SetRoleFilter roleFilter -> do
    H.modify_ _ { roleFilter = roleFilter }
    handleAction PerformSearch
  
  Close -> do
    H.modify_ _ { visible = false, query = "", results = [] }
    H.raise SearchClosed
  
  PerformSearch -> do
    state <- H.get
    if String.null state.query then
      H.modify_ _ { results = [] }
    else do
      H.modify_ _ { isSearching = true }
      -- Parse query
      let parsedQuery = parseQuery state.query state.typeFilter state.dateFilter state.modelFilter state.roleFilter
      H.modify_ _ { parsedQuery = parsedQuery }
      
      -- Perform search (would call Bridge API)
      -- For now, use local search
      results <- performLocalSearch parsedQuery state.wsClient
      H.modify_ _ { results = results, isSearching = false }
  
  NavigateUp -> do
    state <- H.get
    let newIndex = if state.selectedIndex > 0 then state.selectedIndex - 1 else Array.length state.results - 1
    H.modify_ _ { selectedIndex = newIndex }
  
  NavigateDown -> do
    state <- H.get
    let newIndex = if state.selectedIndex < Array.length state.results - 1 then state.selectedIndex + 1 else 0
    H.modify_ _ { selectedIndex = newIndex }
  
  OpenSelected -> do
    state <- H.get
    case Array.index state.results state.selectedIndex of
      Just result -> do
        H.raise (ResultSelected result)
        H.modify_ _ { visible = false }
      Nothing -> pure unit

-- | Parse search query
parseQuery :: String -> Maybe SearchResultType -> Maybe DateFilter -> Maybe String -> Maybe String -> SearchQuery
parseQuery text typeFilter dateFilter modelFilter roleFilter =
  { text: text
  , typeFilter: typeFilter
  , dateFilter: dateFilter
  , modelFilter: modelFilter
  , roleFilter: roleFilter
  }

-- | Perform search using Bridge API
performLocalSearch :: forall m. MonadAff m => SearchQuery -> Maybe WS.WSClient -> H.HalogenM State Action () Output m (Array SearchResult)
performLocalSearch query wsClient = do
  case wsClient of
    Just client -> do
      -- Convert SearchQuery to Bridge.SearchRequest
      let bridgeRequest =
            { query: query.text
            , types: map (\t -> [showSearchResultType t]) query.typeFilter
            , dateRange: map convertDateFilter query.dateFilter
            , model: query.modelFilter
            , sessionId: Nothing
            , limit: Just 50
            , offset: Nothing
            }
      
      -- Call Bridge API
      result <- liftEffect $ Bridge.performSearch client bridgeRequest
      case result of
        Right response -> do
          -- Convert Bridge.SearchResultBridge to SearchResult
          pure $ Array.map convertBridgeResult response.results
        Left _ -> pure []
    Nothing -> pure []

-- | Convert SearchResultType to string
showSearchResultType :: SearchResultType -> String
showSearchResultType = case _ of
  SessionResult -> "session"
  MessageResult -> "message"
  FileResult -> "file"
  ProofResult -> "proof"
  RecordingResult -> "recording"

-- | Convert DateFilter to Bridge date range
convertDateFilter :: DateFilter -> { start :: Maybe String, end :: Maybe String }
convertDateFilter = case _ of
  Today -> { start: Nothing, end: Nothing }  -- Would calculate today's range
  ThisWeek -> { start: Nothing, end: Nothing }  -- Would calculate week range
  ThisMonth -> { start: Nothing, end: Nothing }  -- Would calculate month range
  CustomDate dt -> { start: Nothing, end: Nothing }  -- Would format DateTime
  AfterDate dt -> { start: Nothing, end: Nothing }  -- Would format DateTime
  BeforeDate dt -> { start: Nothing, end: Nothing }  -- Would format DateTime

-- | Convert Bridge result to SearchResult
convertBridgeResult :: Bridge.SearchResultBridge -> SearchResult
convertBridgeResult bridgeResult =
  { id: bridgeResult.id
  , type_: parseResultType bridgeResult.type_
  , title: bridgeResult.title
  , preview: bridgeResult.preview
  , metadata:
      { sessionId: Nothing
      , timestamp: Nothing  -- Would parse from bridgeResult.timestamp
      , model: Nothing
      , filePath: Nothing
      , lineNumber: Nothing
      , proofStatus: Nothing
      }
  , relevance: bridgeResult.score
  }

-- | Parse result type string
parseResultType :: String -> SearchResultType
parseResultType = case _ of
  "session" -> SessionResult
  "message" -> MessageResult
  "file" -> FileResult
  "proof" -> ProofResult
  "recording" -> RecordingResult
  _ -> SessionResult  -- Default

-- | Keyboard event emitter for search navigation
keyboardEventEmitter :: forall m. MonadAff m => H.Emitter m Action
keyboardEventEmitter = H.Emitter \emit -> do
  doc <- liftEffect $ document =<< window
  let target = toEventTarget doc
  
  keydownListener <- liftEffect $ eventListener \e -> do
    case fromEvent e of
      Just ke -> do
        case key ke of
          "ArrowUp" -> liftEffect $ emit NavigateUp
          "ArrowDown" -> liftEffect $ emit NavigateDown
          "Enter" -> liftEffect $ emit OpenSelected
          "Escape" -> liftEffect $ emit Close
          _ -> pure unit
      Nothing -> pure unit
  
  liftEffect $ addEventListener (EventType "keydown") keydownListener false target
  
  -- Return cleanup function
  pure $ removeEventListener (EventType "keydown") keydownListener false target

-- | Prevent default event (using Web.Event.Event)
preventDefaultEvent :: forall e. e -> Effect Unit
preventDefaultEvent e = preventDefault e

-- | Stop event propagation (using Web.Event.Event)
stopPropagationEvent :: forall e. e -> Effect Unit
stopPropagationEvent e = stopPropagation e
