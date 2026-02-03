-- | DropdownMenu Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/dropdown-menu.tsx (309 lines)
-- |
-- | Full-featured dropdown menu with groups, separators, radio groups, and checkbox items.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Data Attributes:
-- | Root:
-- | - `data-component="dropdown-menu"` - Root element
-- | - `data-open="true|false"` - Open state
-- |
-- | Trigger:
-- | - `data-slot="dropdown-menu-trigger"` - Trigger element
-- | - `data-slot="dropdown-menu-icon"` - Icon element
-- |
-- | Content:
-- | - `data-component="dropdown-menu-content"` - Content container
-- | - `data-slot="dropdown-menu-separator"` - Visual separator
-- |
-- | Groups:
-- | - `data-slot="dropdown-menu-group"` - Group container
-- | - `data-slot="dropdown-menu-group-label"` - Group label
-- |
-- | Items:
-- | - `data-slot="dropdown-menu-item"` - Standard item
-- | - `data-slot="dropdown-menu-item-label"` - Item label
-- | - `data-slot="dropdown-menu-item-description"` - Item description
-- | - `data-slot="dropdown-menu-item-indicator"` - Check/radio indicator
-- | - `data-highlighted="true"` - Currently focused item
-- | - `data-disabled="true"` - Disabled item
-- |
-- | Radio/Checkbox:
-- | - `data-slot="dropdown-menu-radio-group"` - Radio group
-- | - `data-slot="dropdown-menu-radio-item"` - Radio option
-- | - `data-slot="dropdown-menu-checkbox-item"` - Checkbox option
-- | - `data-state="checked|unchecked"` - Selection state
module UI.Components.DropdownMenu
  ( component
  , Query(..)
  , Input
  , Output(..)
  , MenuItem(..)
  , MenuGroup
  , Slot
  , defaultInput
  ) where

import Prelude

import Data.Array (findIndex, length, mapWithIndex, updateAt)
import Data.Const (Const)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Void (Void)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Type.Proxy (Proxy(..))
import Web.UIEvent.KeyboardEvent as KE

import UI.Components.Icon as Icon

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Menu item types
data MenuItem
  = ItemAction
      { id :: String
      , label :: String
      , description :: Maybe String
      , icon :: Maybe Icon.IconName
      , disabled :: Boolean
      }
  | ItemCheckbox
      { id :: String
      , label :: String
      , checked :: Boolean
      , disabled :: Boolean
      }
  | ItemRadio
      { id :: String
      , label :: String
      , value :: String
      , disabled :: Boolean
      }
  | ItemSeparator

-- | Menu group with optional label
type MenuGroup =
  { label :: Maybe String
  , items :: Array MenuItem
  , radioGroupName :: Maybe String  -- For radio groups
  , radioValue :: Maybe String      -- Current radio value
  }

-- | DropdownMenu input props
type Input =
  { groups :: Array MenuGroup
  , className :: Maybe String
  }

defaultInput :: Input
defaultInput =
  { groups: []
  , className: Nothing
  }

-- | Output events
data Output
  = ItemClicked String             -- Item ID
  | CheckboxToggled String Boolean -- Item ID, new state
  | RadioSelected String String    -- Group name, value

-- | Queries for external control
data Query a
  = Open a
  | Close a
  | Toggle a
  | IsOpen (Boolean -> a)
  | SetCheckbox String Boolean a
  | SetRadio String String a

-- | Internal state
type State =
  { input :: Input
  , isOpen :: Boolean
  , highlightedIndex :: Maybe Int  -- Flat index across all items
  , groups :: Array MenuGroup      -- Local copy for checkbox/radio state
  }

-- | Internal actions
data Action
  = Initialize
  | HandleTriggerClick
  | HandleItemClick String
  | HandleCheckboxClick String
  | HandleRadioClick String String  -- Group name, value
  | HandleKeyDown KE.KeyboardEvent
  | HandleMouseEnterItem Int
  | HandleClickOutside
  | Receive Input

-- | Slot type for parent components
type Slot id = H.Slot Query Output id

-- | Child slots
type Slots = ( icon :: H.Slot (Const Void) Void String )

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
  , isOpen: false
  , highlightedIndex: Nothing
  , groups: input.groups
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ HP.attr (HH.AttrName "data-component") "dropdown-menu"
    , HP.attr (HH.AttrName "data-open") (if state.isOpen then "true" else "false")
    , HP.attr (HH.AttrName "style") "position: relative; display: inline-block;"
    , HE.onKeyDown HandleKeyDown
    ]
    [ renderTrigger
    , if state.isOpen then renderContent state else HH.text ""
    ]

renderTrigger :: forall m. H.ComponentHTML Action Slots m
renderTrigger =
  HH.button
    [ HP.attr (HH.AttrName "data-slot") "dropdown-menu-trigger"
    , HP.type_ HP.ButtonButton
    , HP.attr (HH.AttrName "aria-haspopup") "menu"
    , HE.onClick \_ -> HandleTriggerClick
    ]
    []  -- Trigger content provided by parent

renderContent :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
renderContent state =
  HH.div
    ([ HP.attr (HH.AttrName "data-component") "dropdown-menu-content"
     , HP.attr (HH.AttrName "role") "menu"
     , HP.attr (HH.AttrName "style") contentStyle
     , HP.tabIndex 0
     ] <> classAttr state.input.className)
    (renderGroups state)
  where
    contentStyle = "position: absolute; top: 100%; left: 0; margin-top: 4px; z-index: 1000;"

renderGroups :: forall m. MonadAff m => State -> Array (H.ComponentHTML Action Slots m)
renderGroups state =
  let indexed = mapWithIndex (\groupIdx group -> renderGroup state groupIdx group) state.groups
  in join indexed

renderGroup :: forall m. MonadAff m => State -> Int -> MenuGroup -> Array (H.ComponentHTML Action Slots m)
renderGroup state groupIdx group =
  let labelEl = case group.label of
        Nothing -> []
        Just l -> 
          [ HH.div
              [ HP.attr (HH.AttrName "data-slot") "dropdown-menu-group-label" ]
              [ HH.text l ]
          ]
      items = mapWithIndex (\itemIdx item -> renderMenuItem state groupIdx itemIdx group item) group.items
  in
    [ HH.div
        [ HP.attr (HH.AttrName "data-slot") (if group.radioGroupName /= Nothing then "dropdown-menu-radio-group" else "dropdown-menu-group")
        , HP.attr (HH.AttrName "role") (if group.radioGroupName /= Nothing then "radiogroup" else "group")
        ]
        (labelEl <> items)
    ]

renderMenuItem :: forall m. MonadAff m => State -> Int -> Int -> MenuGroup -> MenuItem -> H.ComponentHTML Action Slots m
renderMenuItem state groupIdx itemIdx group item =
  let flatIndex = getFlatIndex state.groups groupIdx itemIdx
      isHighlighted = state.highlightedIndex == Just flatIndex
  in case item of
    ItemAction r ->
      HH.div
        [ HP.attr (HH.AttrName "data-slot") "dropdown-menu-item"
        , HP.attr (HH.AttrName "role") "menuitem"
        , HP.attr (HH.AttrName "data-highlighted") (if isHighlighted then "true" else "false")
        , HP.attr (HH.AttrName "data-disabled") (if r.disabled then "true" else "false")
        , HP.tabIndex (if isHighlighted then 0 else (-1))
        , HE.onClick \_ -> if r.disabled then pure unit else HandleItemClick r.id
        , HE.onMouseEnter \_ -> HandleMouseEnterItem flatIndex
        ]
        (iconPart r.icon r.id <> 
         [ HH.span [ HP.attr (HH.AttrName "data-slot") "dropdown-menu-item-label" ] [ HH.text r.label ] ] <>
         descriptionPart r.description)

    ItemCheckbox r ->
      HH.div
        [ HP.attr (HH.AttrName "data-slot") "dropdown-menu-checkbox-item"
        , HP.attr (HH.AttrName "role") "menuitemcheckbox"
        , HP.attr (HH.AttrName "aria-checked") (if r.checked then "true" else "false")
        , HP.attr (HH.AttrName "data-state") (if r.checked then "checked" else "unchecked")
        , HP.attr (HH.AttrName "data-highlighted") (if isHighlighted then "true" else "false")
        , HP.attr (HH.AttrName "data-disabled") (if r.disabled then "true" else "false")
        , HP.tabIndex (if isHighlighted then 0 else (-1))
        , HE.onClick \_ -> if r.disabled then pure unit else HandleCheckboxClick r.id
        , HE.onMouseEnter \_ -> HandleMouseEnterItem flatIndex
        ]
        [ HH.span 
            [ HP.attr (HH.AttrName "data-slot") "dropdown-menu-item-indicator" ] 
            [ if r.checked then HH.text "✓" else HH.text "" ]
        , HH.span [ HP.attr (HH.AttrName "data-slot") "dropdown-menu-item-label" ] [ HH.text r.label ]
        ]

    ItemRadio r ->
      let isChecked = group.radioValue == Just r.value
      in HH.div
        [ HP.attr (HH.AttrName "data-slot") "dropdown-menu-radio-item"
        , HP.attr (HH.AttrName "role") "menuitemradio"
        , HP.attr (HH.AttrName "aria-checked") (if isChecked then "true" else "false")
        , HP.attr (HH.AttrName "data-state") (if isChecked then "checked" else "unchecked")
        , HP.attr (HH.AttrName "data-highlighted") (if isHighlighted then "true" else "false")
        , HP.attr (HH.AttrName "data-disabled") (if r.disabled then "true" else "false")
        , HP.tabIndex (if isHighlighted then 0 else (-1))
        , HE.onClick \_ -> case group.radioGroupName of
            Just name -> if r.disabled then pure unit else HandleRadioClick name r.value
            Nothing -> pure unit
        , HE.onMouseEnter \_ -> HandleMouseEnterItem flatIndex
        ]
        [ HH.span 
            [ HP.attr (HH.AttrName "data-slot") "dropdown-menu-item-indicator" ] 
            [ if isChecked then HH.text "●" else HH.text "○" ]
        , HH.span [ HP.attr (HH.AttrName "data-slot") "dropdown-menu-item-label" ] [ HH.text r.label ]
        ]

    ItemSeparator ->
      HH.hr [ HP.attr (HH.AttrName "data-slot") "dropdown-menu-separator" ]

iconPart :: forall m. MonadAff m => Maybe Icon.IconName -> String -> Array (H.ComponentHTML Action Slots m)
iconPart Nothing _ = []
iconPart (Just iconName) itemId =
  [ HH.slot_ (Proxy :: Proxy "icon") itemId Icon.component
      { name: iconName
      , size: Icon.Small
      , className: Nothing
      }
  ]

descriptionPart :: forall m. Maybe String -> Array (H.ComponentHTML Action Slots m)
descriptionPart Nothing = []
descriptionPart (Just desc) =
  [ HH.span [ HP.attr (HH.AttrName "data-slot") "dropdown-menu-item-description" ] [ HH.text desc ] ]

classAttr :: forall r i. Maybe String -> Array (HP.IProp r i)
classAttr Nothing = []
classAttr (Just cls) = [ HP.class_ (HH.ClassName cls) ]

-- Helper to get flat index from group/item indices
getFlatIndex :: Array MenuGroup -> Int -> Int -> Int
getFlatIndex groups groupIdx itemIdx =
  let previousGroups = take groupIdx groups
      previousCount = sum (map (\g -> length g.items) previousGroups)
  in previousCount + itemIdx
  where
    take :: forall a. Int -> Array a -> Array a
    take n arr = takeImpl n arr
    
    sum :: Array Int -> Int
    sum = foldr (+) 0

foreign import takeImpl :: forall a. Int -> Array a -> Array a

-- Helper to get total item count
getTotalItemCount :: Array MenuGroup -> Int
getTotalItemCount groups = sum (map (\g -> length g.items) groups)
  where
    sum = foldr (+) 0

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize ->
    pure unit

  HandleTriggerClick -> do
    H.modify_ \st -> st { isOpen = not st.isOpen, highlightedIndex = Nothing }

  HandleItemClick itemId -> do
    H.modify_ _ { isOpen = false }
    H.raise (ItemClicked itemId)

  HandleCheckboxClick itemId -> do
    -- Toggle checkbox state
    state <- H.get
    let newGroups = map (updateCheckbox itemId) state.groups
    H.modify_ _ { groups = newGroups }
    -- Find new state and raise event
    let newChecked = findCheckboxState itemId newGroups
    H.raise (CheckboxToggled itemId (fromMaybe false newChecked))

  HandleRadioClick groupName value -> do
    -- Update radio state
    state <- H.get
    let newGroups = map (updateRadio groupName value) state.groups
    H.modify_ _ { groups = newGroups, isOpen = false }
    H.raise (RadioSelected groupName value)

  HandleKeyDown ke -> do
    state <- H.get
    when state.isOpen do
      case KE.key ke of
        "Escape" -> do
          liftEffect $ KE.preventDefault ke
          H.modify_ _ { isOpen = false, highlightedIndex = Nothing }
        
        "ArrowDown" -> do
          liftEffect $ KE.preventDefault ke
          let total = getTotalItemCount state.groups
              next = case state.highlightedIndex of
                Nothing -> 0
                Just i -> min (i + 1) (total - 1)
          H.modify_ _ { highlightedIndex = Just next }
        
        "ArrowUp" -> do
          liftEffect $ KE.preventDefault ke
          let total = getTotalItemCount state.groups
              prev = case state.highlightedIndex of
                Nothing -> total - 1
                Just i -> max (i - 1) 0
          H.modify_ _ { highlightedIndex = Just prev }
        
        "Enter" -> do
          liftEffect $ KE.preventDefault ke
          -- Activate highlighted item
          case state.highlightedIndex of
            Just idx -> activateItemAtIndex idx
            Nothing -> pure unit
        
        " " -> do  -- Space
          liftEffect $ KE.preventDefault ke
          case state.highlightedIndex of
            Just idx -> activateItemAtIndex idx
            Nothing -> pure unit
        
        _ -> pure unit

  HandleMouseEnterItem idx ->
    H.modify_ _ { highlightedIndex = Just idx }

  HandleClickOutside ->
    H.modify_ _ { isOpen = false, highlightedIndex = Nothing }

  Receive newInput ->
    H.modify_ _ { input = newInput, groups = newInput.groups }

-- Helper to update checkbox in groups
updateCheckbox :: String -> MenuGroup -> MenuGroup
updateCheckbox itemId group =
  group { items = map (toggleCheckbox itemId) group.items }

toggleCheckbox :: String -> MenuItem -> MenuItem
toggleCheckbox targetId item = case item of
  ItemCheckbox r | r.id == targetId -> ItemCheckbox (r { checked = not r.checked })
  _ -> item

-- Helper to find checkbox state
findCheckboxState :: String -> Array MenuGroup -> Maybe Boolean
findCheckboxState itemId groups =
  let allItems = join (map _.items groups)
  in case findIndex (isCheckboxWithId itemId) allItems of
    Just idx -> case allItems !! idx of
      Just (ItemCheckbox r) -> Just r.checked
      _ -> Nothing
    Nothing -> Nothing

isCheckboxWithId :: String -> MenuItem -> Boolean
isCheckboxWithId targetId (ItemCheckbox r) = r.id == targetId
isCheckboxWithId _ _ = false

-- Helper to update radio in groups
updateRadio :: String -> String -> MenuGroup -> MenuGroup
updateRadio groupName value group =
  if group.radioGroupName == Just groupName
    then group { radioValue = Just value }
    else group

-- Helper to activate item at flat index
activateItemAtIndex :: forall m. MonadAff m => Int -> H.HalogenM State Action Slots Output m Unit
activateItemAtIndex targetIdx = do
  state <- H.get
  let mItem = getItemAtFlatIndex state.groups targetIdx
  case mItem of
    Just (ItemAction r) | not r.disabled -> handleAction (HandleItemClick r.id)
    Just (ItemCheckbox r) | not r.disabled -> handleAction (HandleCheckboxClick r.id)
    Just (ItemRadio r) | not r.disabled -> do
      let mGroupName = getRadioGroupNameForIndex state.groups targetIdx
      case mGroupName of
        Just name -> handleAction (HandleRadioClick name r.value)
        Nothing -> pure unit
    _ -> pure unit

-- Helper to get item at flat index
getItemAtFlatIndex :: Array MenuGroup -> Int -> Maybe MenuItem
getItemAtFlatIndex groups targetIdx =
  let allItems = join (map _.items groups)
  in allItems !! targetIdx

-- Helper to get radio group name for item at index
getRadioGroupNameForIndex :: Array MenuGroup -> Int -> Maybe String
getRadioGroupNameForIndex groups targetIdx =
  go groups 0
  where
    go :: Array MenuGroup -> Int -> Maybe String
    go [] _ = Nothing
    go gs currentIdx = case gs !! 0 of
      Nothing -> Nothing
      Just g ->
        let groupLen = length g.items
        in if targetIdx < currentIdx + groupLen
           then g.radioGroupName
           else go (fromMaybe [] (deleteAt 0 gs)) (currentIdx + groupLen)
    
    deleteAt :: forall a. Int -> Array a -> Maybe (Array a)
    deleteAt = deleteAtImpl

foreign import deleteAtImpl :: forall a. Int -> Array a -> Maybe (Array a)

-- Array indexing
infixl 8 indexArray as !!

indexArray :: forall a. Array a -> Int -> Maybe a
indexArray = indexArrayImpl

foreign import indexArrayImpl :: forall a. Array a -> Int -> Maybe a

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
handleQuery = case _ of
  Open a -> do
    H.modify_ _ { isOpen = true, highlightedIndex = Nothing }
    pure (Just a)

  Close a -> do
    H.modify_ _ { isOpen = false, highlightedIndex = Nothing }
    pure (Just a)

  Toggle a -> do
    H.modify_ \st -> st { isOpen = not st.isOpen, highlightedIndex = Nothing }
    pure (Just a)

  IsOpen reply -> do
    state <- H.get
    pure (Just (reply state.isOpen))

  SetCheckbox itemId checked a -> do
    state <- H.get
    let newGroups = map (setCheckboxValue itemId checked) state.groups
    H.modify_ _ { groups = newGroups }
    pure (Just a)

  SetRadio groupName value a -> do
    state <- H.get
    let newGroups = map (updateRadio groupName value) state.groups
    H.modify_ _ { groups = newGroups }
    pure (Just a)

setCheckboxValue :: String -> Boolean -> MenuGroup -> MenuGroup
setCheckboxValue itemId newChecked group =
  group { items = map (setCheckbox itemId newChecked) group.items }

setCheckbox :: String -> Boolean -> MenuItem -> MenuItem
setCheckbox targetId newChecked item = case item of
  ItemCheckbox r | r.id == targetId -> ItemCheckbox (r { checked = newChecked })
  _ -> item

-- ═══════════════════════════════════════════════════════════════════════════════
-- MINIMAL FFI
-- ═══════════════════════════════════════════════════════════════════════════════
-- Array utilities
