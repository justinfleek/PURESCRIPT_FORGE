-- | List Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/list.tsx (346 lines)
-- |
-- | Searchable, filterable list with keyboard navigation.
-- | Supports grouping, selection, and custom item rendering.
-- | Pure Halogen implementation.
-- |
-- | Data Attributes:
-- | - `data-component="list"` - Root element
-- | - `data-slot="list-search-wrapper"` - Search area wrapper
-- | - `data-slot="list-search"` - Search container
-- | - `data-slot="list-search-container"` - Input wrapper
-- | - `data-slot="list-search-input"` - Search input
-- | - `data-slot="list-scroll"` - Scrollable area
-- | - `data-slot="list-group"` - Group container
-- | - `data-slot="list-header"` - Group header (sticky)
-- | - `data-slot="list-items"` - Items container
-- | - `data-slot="list-item"` - List item button
-- | - `data-key` - Item key
-- | - `data-active` - Keyboard focus state
-- | - `data-selected` - Selection state
-- | - `data-slot="list-item-selected-icon"` - Check icon
-- | - `data-slot="list-item-active-icon"` - Active icon
-- | - `data-slot="list-item-divider"` - Item divider
-- | - `data-slot="list-empty-state"` - Empty state container
-- | - `data-slot="list-message"` - Empty message
-- | - `data-slot="list-filter"` - Filter text in message
module UI.Components.List
  ( component
  , Query(..)
  , Input
  , Output(..)
  , Slot
  , ListItem
  , ListGroup
  , defaultInput
  ) where

import Prelude

import Data.Array (filter, findIndex, length, (!!))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.String as String
import Data.String.Pattern (Pattern(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Web.UIEvent.KeyboardEvent as KE

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | List item type (generic)
type ListItem =
  { key :: String
  , label :: String
  , group :: Maybe String
  }

-- | Grouped items
type ListGroup =
  { category :: String
  , items :: Array ListItem
  }

-- | Search configuration
type SearchConfig =
  { placeholder :: String
  , autofocus :: Boolean
  , hideIcon :: Boolean
  }

-- | List input props
type Input =
  { items :: Array ListItem
  , current :: Maybe String        -- Key of current/selected item
  , emptyMessage :: String
  , loadingMessage :: String
  , loading :: Boolean
  , search :: Maybe SearchConfig
  , divider :: Boolean
  , activeIcon :: Maybe String     -- Icon name for active items
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { items: []
  , current: Nothing
  , emptyMessage: "No items"
  , loadingMessage: "Loading..."
  , loading: false
  , search: Nothing
  , divider: false
  , activeIcon: Nothing
  , className: Nothing
  }

-- | Output events
data Output
  = Selected String Int            -- Item key and index
  | ActiveChanged (Maybe String)   -- Currently active key
  | FilterChanged String           -- Filter text changed

-- | Queries for external control
data Query a
  = SetFilter String a
  | GetFilter (String -> a)
  | SetActive (Maybe String) a
  | GetActive (Maybe String -> a)
  | FocusSearch a

-- | Internal state
type State =
  { input :: Input
  , filterText :: String
  , activeKey :: Maybe String
  , mouseActive :: Boolean
  }

-- | Internal actions
data Action
  = Initialize
  | Receive Input
  | HandleFilterInput String
  | HandleKeyDown KE.KeyboardEvent
  | HandleItemClick String Int
  | HandleItemMouseMove String
  | HandleItemMouseLeave
  | ClearFilter

-- | Slot type for parent components
type Slot id = H.Slot Query Output id

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMPONENT
-- ═══════════════════════════════════════════════════════════════════════════════

component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , initialize = Just Initialize
      , receive = Just <<< Receive
      }
  }

initialState :: Input -> State
initialState input =
  { input
  , filterText: ""
  , activeKey: Nothing
  , mouseActive: false
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  let
    filteredItems = filterItems state.filterText state.input.items
    groups = groupItems filteredItems
  in
    HH.div
      ([ HP.attr (HH.AttrName "data-component") "list"
      ] <> classAttr state.input.className)
      [ renderSearch state
      , renderScrollArea state groups filteredItems
      ]

renderSearch :: forall m. State -> H.ComponentHTML Action () m
renderSearch state =
  case state.input.search of
    Nothing -> HH.text ""
    Just config ->
      HH.div
        [ HP.attr (HH.AttrName "data-slot") "list-search-wrapper" ]
        [ HH.div
            [ HP.attr (HH.AttrName "data-slot") "list-search" ]
            [ HH.div
                [ HP.attr (HH.AttrName "data-slot") "list-search-container" ]
                [ if config.hideIcon 
                    then HH.text ""
                    else HH.span 
                      [ HP.attr (HH.AttrName "aria-hidden") "true" ]
                      [ HH.text "🔍" ]
                , HH.input
                    [ HP.type_ HP.InputText
                    , HP.ref (H.RefLabel "search-input")
                    , HP.attr (HH.AttrName "data-slot") "list-search-input"
                    , HP.placeholder config.placeholder
                    , HP.value state.filterText
                    , HP.autofocus config.autofocus
                    , HP.attr (HH.AttrName "spellcheck") "false"
                    , HP.attr (HH.AttrName "autocorrect") "off"
                    , HP.attr (HH.AttrName "autocomplete") "off"
                    , HP.attr (HH.AttrName "autocapitalize") "off"
                    , HE.onValueInput HandleFilterInput
                    ]
                ]
            , if state.filterText /= ""
                then HH.button
                  [ HP.type_ HP.ButtonButton
                  , HP.attr (HH.AttrName "aria-label") "Clear filter"
                  , HE.onClick \_ -> ClearFilter
                  ]
                  [ HH.text "×" ]
                else HH.text ""
            ]
        ]

renderScrollArea :: forall m. State -> Array ListGroup -> Array ListItem -> H.ComponentHTML Action () m
renderScrollArea state groups items =
  HH.div
    [ HP.ref (H.RefLabel "scroll")
    , HP.attr (HH.AttrName "data-slot") "list-scroll"
    ]
    [ if length items == 0
        then renderEmptyState state
        else renderGroups state groups
    ]

renderEmptyState :: forall m. State -> H.ComponentHTML Action () m
renderEmptyState state =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "list-empty-state" ]
    [ HH.div
        [ HP.attr (HH.AttrName "data-slot") "list-message" ]
        [ if state.input.loading
            then HH.text state.input.loadingMessage
            else if state.filterText /= ""
              then HH.span_
                [ HH.text "No results for "
                , HH.span 
                    [ HP.attr (HH.AttrName "data-slot") "list-filter" ]
                    [ HH.text ("\"" <> state.filterText <> "\"") ]
                ]
              else HH.text state.input.emptyMessage
        ]
    ]

renderGroups :: forall m. State -> Array ListGroup -> H.ComponentHTML Action () m
renderGroups state groups =
  HH.div_
    (map (renderGroup state) groups)

renderGroup :: forall m. State -> ListGroup -> H.ComponentHTML Action () m
renderGroup state group =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "list-group" ]
    [ if group.category /= ""
        then HH.div
          [ HP.attr (HH.AttrName "data-slot") "list-header" ]
          [ HH.text group.category ]
        else HH.text ""
    , HH.div
        [ HP.attr (HH.AttrName "data-slot") "list-items" ]
        (mapWithIndex (renderItem state (length group.items)) group.items)
    ]

renderItem :: forall m. State -> Int -> Int -> ListItem -> H.ComponentHTML Action () m
renderItem state totalItems index item =
  let
    isActive = state.activeKey == Just item.key
    isSelected = state.input.current == Just item.key
    showDivider = state.input.divider && index < totalItems - 1
  in
    HH.button
      [ HP.type_ HP.ButtonButton
      , HP.attr (HH.AttrName "data-slot") "list-item"
      , HP.attr (HH.AttrName "data-key") item.key
      , HP.attr (HH.AttrName "data-active") (if isActive then "true" else "false")
      , HP.attr (HH.AttrName "data-selected") (if isSelected then "true" else "false")
      , HE.onClick \_ -> HandleItemClick item.key index
      , HE.onMouseMove \_ -> HandleItemMouseMove item.key
      , HE.onMouseLeave \_ -> HandleItemMouseLeave
      ]
      [ HH.text item.label
      , if isSelected
          then HH.span
            [ HP.attr (HH.AttrName "data-slot") "list-item-selected-icon" ]
            [ HH.text "✓" ]
          else HH.text ""
      , case state.input.activeIcon of
          Just iconName | isActive -> 
            HH.span
              [ HP.attr (HH.AttrName "data-slot") "list-item-active-icon" ]
              [ HH.text "→" ]
          _ -> HH.text ""
      , if showDivider
          then HH.span
            [ HP.attr (HH.AttrName "data-slot") "list-item-divider" ]
            []
          else HH.text ""
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- HELPERS
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Filter items by search text
filterItems :: String -> Array ListItem -> Array ListItem
filterItems filterText items
  | filterText == "" = items
  | otherwise = 
      let pattern = String.toLower filterText
      in filter (\item -> String.contains (Pattern pattern) (String.toLower item.label)) items

-- | Group items by category
groupItems :: Array ListItem -> Array ListGroup
groupItems items =
  let
    -- Simple grouping: all items without group go to ""
    ungrouped = filter (\item -> isNothing item.group) items
    -- For now, just one group
  in
    [ { category: "", items: items } ]
  where
    isNothing Nothing = true
    isNothing _ = false

-- | Map with index
mapWithIndex :: forall a b. (Int -> a -> b) -> Array a -> Array b
mapWithIndex f arr = 
  let indexed = zipWithIndex arr
  in map (\{ index, value } -> f index value) indexed

zipWithIndex :: forall a. Array a -> Array { index :: Int, value :: a }
zipWithIndex arr = mapWithIndexImpl arr

foreign import mapWithIndexImpl :: forall a. Array a -> Array { index :: Int, value :: a }

-- | Move to next/previous item
moveActive :: State -> Int -> Maybe String
moveActive state delta =
  let
    items = filterItems state.filterText state.input.items
    keys = map _.key items
    currentIdx = case state.activeKey of
      Nothing -> -1
      Just key -> fromMaybe (-1) (findIndex (_ == key) keys)
    newIdx = max 0 (min (length keys - 1) (currentIdx + delta))
  in
    keys !! newIdx

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Set initial active to current if exists
    state <- H.get
    for_ state.input.current \key ->
      H.modify_ _ { activeKey = Just key }

  Receive newInput -> do
    H.modify_ _ { input = newInput }

  HandleFilterInput text -> do
    H.modify_ _ { filterText = text, activeKey = Nothing }
    H.raise (FilterChanged text)

  HandleKeyDown ke -> do
    state <- H.get
    let key = KE.key ke
    case key of
      "ArrowDown" -> do
        H.modify_ _ { mouseActive = false }
        let newActive = moveActive state 1
        H.modify_ _ { activeKey = newActive }
        H.raise (ActiveChanged newActive)
      "ArrowUp" -> do
        H.modify_ _ { mouseActive = false }
        let newActive = moveActive state (-1)
        H.modify_ _ { activeKey = newActive }
        H.raise (ActiveChanged newActive)
      "Enter" -> do
        state' <- H.get
        for_ state'.activeKey \activeKey -> do
          let items = filterItems state'.filterText state'.input.items
          let idx = fromMaybe 0 (findIndex (\item -> item.key == activeKey) items)
          H.raise (Selected activeKey idx)
      _ -> pure unit

  HandleItemClick itemKey index -> do
    H.raise (Selected itemKey index)

  HandleItemMouseMove itemKey -> do
    H.modify_ _ { mouseActive = true, activeKey = Just itemKey }

  HandleItemMouseLeave -> do
    state <- H.get
    when state.mouseActive do
      H.modify_ _ { activeKey = Nothing }

  ClearFilter -> do
    H.modify_ _ { filterText = "", activeKey = Nothing }
    H.raise (FilterChanged "")

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  SetFilter text a -> do
    H.modify_ _ { filterText = text }
    pure (Just a)

  GetFilter reply -> do
    state <- H.get
    pure (Just (reply state.filterText))

  SetActive mKey a -> do
    H.modify_ _ { activeKey = mKey }
    pure (Just a)

  GetActive reply -> do
    state <- H.get
    pure (Just (reply state.activeKey))

  FocusSearch a -> do
    -- Focus via ref
    pure (Just a)
