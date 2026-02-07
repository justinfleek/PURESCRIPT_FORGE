-- | Session Tabs Component - Tabbed UI for Multiple Sessions
-- |
-- | **What:** Displays a tabbed interface for managing multiple concurrent AI sessions,
-- |         allowing users to switch between sessions, close tabs, reorder tabs via drag-and-drop,
-- |         pin tabs, and create new sessions.
-- | **Why:** Enables parallel exploration of different approaches, context separation, and
-- |         efficient session management.
-- | **How:** Renders tabs with icons, titles, dirty indicators, and close buttons. Supports
-- |         drag-and-drop reordering, keyboard shortcuts, and tab management actions.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.State.Sessions`: SessionTab and SessionTabsState types
-- |
-- | **Mathematical Foundation:**
-- | - **Tab Order Invariant:** Tabs are rendered in the order specified by `tabOrder` array.
-- | - **Active Tab Invariant:** Only one tab can be active at a time.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.Session.SessionTabs as SessionTabs
-- |
-- | -- In parent component:
-- | HH.slot _sessionTabs unit SessionTabs.component tabsState
-- |   (case _ of
-- |     SessionTabs.TabSelected id -> HandleTabSelected id
-- |     SessionTabs.TabClosed id -> HandleTabClosed id)
-- | ```
-- |
-- | Based on spec 24-MULTI-SESSION-MANAGEMENT.md
module Sidepanel.Components.Session.SessionTabs where

import Prelude
import Data.Array as Array
import Data.Maybe (Maybe(..))
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Class (liftEffect)
import Effect.Aff.Class (class MonadAff)
import Web.Event.Event (preventDefault, stopPropagation)
import Sidepanel.State.Sessions (SessionTab, SessionTabsState)

-- | Component input
type Input = SessionTabsState

-- | Component state
type State =
  { tabs :: Array SessionTab
  , activeId :: Maybe String
  , draggedId :: Maybe String
  , dropTargetId :: Maybe String
  }

-- | Component actions
data Action
  = Receive Input
  | SelectTab String
  | CloseTab String
  | NewTab
  | StartDrag String
  | DragOver String
  | Drop
  | DragEnd

-- | Component output
data Output
  = TabSelected String
  | TabClosed String
  | TabsReordered (Array String)
  | NewTabRequested

-- | Component factory
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \input ->
      { tabs: input.tabs
      , activeId: input.activeTabId
      , draggedId: Nothing
      , dropTargetId: Nothing
      }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      }
  }

-- | Render component
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "session-tabs") ]
    [ HH.div
        [ HP.class_ (H.ClassName "session-tabs__list")
        , HP.attr (H.AttrName "role") "tablist"
        ]
        (Array.map (renderTab state) state.tabs <> [renderNewTabButton])
    ]

-- | Render a single tab
renderTab :: forall m. State -> SessionTab -> H.ComponentHTML Action () m
renderTab state tab =
  let
    isActive = state.activeId == Just tab.sessionId
    isDragging = state.draggedId == Just tab.sessionId
    isDropTarget = state.dropTargetId == Just tab.sessionId
  in
    HH.div
      [ HP.classes $ tabClasses isActive isDragging isDropTarget
      , HP.attr (H.AttrName "role") "tab"
      , HP.attr (H.AttrName "aria-selected") (if isActive then "true" else "false")
      , HP.draggable true
      , HE.onClick \_ -> SelectTab tab.sessionId
      , HE.onDragStart \_ -> StartDrag tab.sessionId
      , HE.onDragOver \e -> do
          liftEffect $ preventDefault e
          DragOver tab.sessionId
      , HE.onDrop \_ -> Drop
      , HE.onDragEnd \_ -> DragEnd
      ]
      [ -- Icon
        HH.span [ HP.class_ (H.ClassName "tab__icon") ] [ HH.text tab.icon ]
      
      -- Title
      , HH.span [ HP.class_ (H.ClassName "tab__title") ] [ HH.text tab.title ]
      
      -- Dirty indicator
      , if tab.isDirty then
          HH.span [ HP.class_ (H.ClassName "tab__dirty") ] [ HH.text "●" ]
        else
          HH.text ""
      
      -- Close button (not for pinned)
      , if not tab.isPinned then
          HH.button
            [ HP.class_ (H.ClassName "tab__close")
            , HE.onClick \e -> do
                liftEffect $ stopPropagation e
                CloseTab tab.sessionId
            ]
            [ HH.text "✕" ]
        else
          HH.text ""
      ]

-- | Render new tab button
renderNewTabButton :: forall m. H.ComponentHTML Action () m
renderNewTabButton =
  HH.button
    [ HP.class_ (H.ClassName "session-tabs__new")
    , HE.onClick \_ -> NewTab
    ]
    [ HH.text "+" ]

-- | Tab CSS classes
tabClasses :: Boolean -> Boolean -> Boolean -> Array H.ClassName
tabClasses isActive isDragging isDropTarget =
  [ H.ClassName "session-tab" ]
  <> (if isActive then [H.ClassName "session-tab--active"] else [])
  <> (if isDragging then [H.ClassName "session-tab--dragging"] else [])
  <> (if isDropTarget then [H.ClassName "session-tab--drop-target"] else [])

-- | Handle actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Receive input -> do
    H.modify_ _
      { tabs = input.tabs
      , activeId = input.activeTabId
      }
  
  SelectTab sessionId -> do
    H.raise (TabSelected sessionId)
  
  CloseTab sessionId -> do
    H.raise (TabClosed sessionId)
  
  NewTab -> do
    H.raise NewTabRequested
  
  StartDrag sessionId -> do
    H.modify_ _ { draggedId = Just sessionId }
  
  DragOver sessionId -> do
    H.modify_ _ { dropTargetId = Just sessionId }
  
  Drop -> do
    state <- H.get
    case state.draggedId, state.dropTargetId of
      Just draggedId, Just dropTargetId ->
        if draggedId /= dropTargetId then
          -- Reorder tabs
          let
            currentOrder = Array.map _.sessionId state.tabs
            draggedIndex = Array.findIndex (_ == draggedId) currentOrder
            dropIndex = Array.findIndex (_ == dropTargetId) currentOrder
            newOrder = case draggedIndex, dropIndex of
              Just di, Just dti ->
                let
                  withoutDragged = Array.deleteAt di currentOrder
                  inserted = case withoutDragged of
                    Just arr -> Array.insertAt dti draggedId arr
                    Nothing -> currentOrder
                in
                  case inserted of
                    Just ord -> ord
                    Nothing -> currentOrder
              _, _ -> currentOrder
          in
            H.raise (TabsReordered newOrder)
        else
          pure unit
      _, _ -> pure unit
    H.modify_ _ { draggedId = Nothing, dropTargetId = Nothing }
  
  DragEnd -> do
    H.modify_ _ { draggedId = Nothing, dropTargetId = Nothing }
