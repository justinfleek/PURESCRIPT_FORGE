-- | Toast Component
-- |
-- | Migrated from: forge-dev/packages/ui/src/components/toast.tsx (186 lines)
-- |
-- | Toast notification system with variants and actions.
-- | Pure Halogen implementation - no React, no Kobalte dependency.
-- |
-- | Data Attributes:
-- | Region:
-- | - `data-component="toast-region"` - Container
-- | - `data-slot="toast-list"` - List of toasts
-- |
-- | Toast:
-- | - `data-component="toast"` - Toast root
-- | - `data-variant="default|success|error|loading"` - Visual variant
-- |
-- | Content:
-- | - `data-slot="toast-icon"` - Icon container
-- | - `data-slot="toast-content"` - Content wrapper
-- | - `data-slot="toast-title"` - Title text
-- | - `data-slot="toast-description"` - Description text
-- | - `data-slot="toast-actions"` - Action buttons container
-- | - `data-slot="toast-action"` - Action button
-- | - `data-slot="toast-close-button"` - Close button
-- |
-- | Progress:
-- | - `data-slot="toast-progress-track"` - Progress background
-- | - `data-slot="toast-progress-fill"` - Progress fill
module UI.Components.Toast
  ( component
  , Query(..)
  , Input
  , Output(..)
  , ToastVariant(..)
  , ToastAction
  , Slot
  , defaultInput
  ) where

import Prelude

import Data.Array (deleteAt, findIndex, snoc, (!!))
import Data.Const (Const)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Void (Void)
import Effect.Aff (Milliseconds(..), delay)
import Effect.Aff.Class (class MonadAff, liftAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Type.Proxy (Proxy(..))

import UI.Components.Icon as Icon
import UI.Components.IconButton as IconButton

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Toast visual variants
data ToastVariant
  = Default
  | Success
  | Error
  | Loading

derive instance eqToastVariant :: Eq ToastVariant

variantToString :: ToastVariant -> String
variantToString Default = "default"
variantToString Success = "success"
variantToString Error = "error"
variantToString Loading = "loading"

-- | Toast action button configuration
type ToastAction =
  { label :: String
  , actionId :: String  -- Identifier for the action
  }

-- | Individual toast configuration
type ToastConfig =
  { id :: String
  , title :: Maybe String
  , description :: Maybe String
  , icon :: Maybe Icon.IconName
  , variant :: ToastVariant
  , duration :: Int              -- Duration in ms (0 = persistent)
  , persistent :: Boolean
  , actions :: Array ToastAction
  , progress :: Number           -- 0.0 to 1.0
  }

-- | Toast Region input (container for all toasts)
type Input =
  { maxToasts :: Int
  , position :: ToastPosition
  }

data ToastPosition
  = TopRight
  | TopLeft
  | BottomRight
  | BottomLeft

derive instance eqToastPosition :: Eq ToastPosition

positionToStyle :: ToastPosition -> String
positionToStyle TopRight = "position: fixed; top: 16px; right: 16px; z-index: 9999;"
positionToStyle TopLeft = "position: fixed; top: 16px; left: 16px; z-index: 9999;"
positionToStyle BottomRight = "position: fixed; bottom: 16px; right: 16px; z-index: 9999;"
positionToStyle BottomLeft = "position: fixed; bottom: 16px; left: 16px; z-index: 9999;"

defaultInput :: Input
defaultInput =
  { maxToasts: 5
  , position: BottomRight
  }

-- | Output events
data Output
  = ToastDismissed String           -- Toast ID
  | ToastActionClicked String String -- Toast ID, Action ID

-- | Queries for external control
data Query a
  = ShowToast ToastConfig a
  | DismissToast String a
  | DismissAll a
  | GetActiveToasts (Array String -> a)

-- | Internal state
type State =
  { input :: Input
  , toasts :: Array ToastConfig
  , nextId :: Int
  }

-- | Internal actions
data Action
  = Initialize
  | DismissToastAction String
  | HandleActionClick String String  -- Toast ID, Action ID
  | UpdateProgress String Number
  | AutoDismiss String
  | Receive Input

-- | Slot type for parent components
type Slot id = H.Slot Query Output id

-- | Child slots
type Slots =
  ( icon :: H.Slot (Const Void) Void String
  , closeButton :: H.Slot IconButton.Query IconButton.Output String
  )

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
  , toasts: []
  , nextId: 1
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. MonadAff m => State -> H.ComponentHTML Action Slots m
render state =
  HH.div
    [ HP.attr (HH.AttrName "data-component") "toast-region"
    , HP.attr (HH.AttrName "style") (positionToStyle state.input.position)
    , HP.attr (HH.AttrName "role") "region"
    , HP.attr (HH.AttrName "aria-live") "polite"
    , HP.attr (HH.AttrName "aria-label") "Notifications"
    ]
    [ HH.ol
        [ HP.attr (HH.AttrName "data-slot") "toast-list"
        , HP.attr (HH.AttrName "style") "list-style: none; margin: 0; padding: 0; display: flex; flex-direction: column; gap: 8px;"
        ]
        (map renderToast state.toasts)
    ]

renderToast :: forall m. MonadAff m => ToastConfig -> H.ComponentHTML Action Slots m
renderToast toast =
  HH.li
    [ HP.attr (HH.AttrName "data-component") "toast"
    , HP.attr (HH.AttrName "data-variant") (variantToString toast.variant)
    , HP.attr (HH.AttrName "role") "alert"
    ]
    (iconSection toast <>
     [ contentSection toast
     , closeButtonSection toast
     ] <>
     progressSection toast)

iconSection :: forall m. MonadAff m => ToastConfig -> Array (H.ComponentHTML Action Slots m)
iconSection toast =
  case toast.icon of
    Nothing -> []
    Just iconName ->
      [ HH.div
          [ HP.attr (HH.AttrName "data-slot") "toast-icon" ]
          [ HH.slot_ (Proxy :: Proxy "icon") toast.id Icon.component
              { name: iconName
              , size: Icon.Normal
              , className: Nothing
              }
          ]
      ]

contentSection :: forall m. ToastConfig -> H.ComponentHTML Action Slots m
contentSection toast =
  HH.div
    [ HP.attr (HH.AttrName "data-slot") "toast-content" ]
    (titleSection toast <> descriptionSection toast <> actionsSection toast)

titleSection :: forall m. ToastConfig -> Array (H.ComponentHTML Action Slots m)
titleSection toast =
  case toast.title of
    Nothing -> []
    Just t ->
      [ HH.div
          [ HP.attr (HH.AttrName "data-slot") "toast-title" ]
          [ HH.text t ]
      ]

descriptionSection :: forall m. ToastConfig -> Array (H.ComponentHTML Action Slots m)
descriptionSection toast =
  case toast.description of
    Nothing -> []
    Just d ->
      [ HH.div
          [ HP.attr (HH.AttrName "data-slot") "toast-description" ]
          [ HH.text d ]
      ]

actionsSection :: forall m. ToastConfig -> Array (H.ComponentHTML Action Slots m)
actionsSection toast =
  case toast.actions of
    [] -> []
    actions ->
      [ HH.div
          [ HP.attr (HH.AttrName "data-slot") "toast-actions" ]
          (map (renderAction toast.id) actions)
      ]

renderAction :: forall m. String -> ToastAction -> H.ComponentHTML Action Slots m
renderAction toastId action =
  HH.button
    [ HP.attr (HH.AttrName "data-slot") "toast-action"
    , HP.type_ HP.ButtonButton
    , HE.onClick \_ -> HandleActionClick toastId action.actionId
    ]
    [ HH.text action.label ]

closeButtonSection :: forall m. MonadAff m => ToastConfig -> H.ComponentHTML Action Slots m
closeButtonSection toast =
  HH.slot (Proxy :: Proxy "closeButton") toast.id IconButton.component
    { icon: "close"
    , size: IconButton.Normal
    , iconSize: Nothing
    , variant: IconButton.Ghost
    , disabled: false
    , ariaLabel: "Dismiss"
    , className: Nothing
    }
    (handleCloseOutput toast.id)

handleCloseOutput :: String -> IconButton.Output -> Action
handleCloseOutput toastId IconButton.Clicked = DismissToastAction toastId

progressSection :: forall m. ToastConfig -> Array (H.ComponentHTML Action Slots m)
progressSection toast
  | toast.persistent = []
  | otherwise =
      [ HH.div
          [ HP.attr (HH.AttrName "data-slot") "toast-progress-track" ]
          [ HH.div
              [ HP.attr (HH.AttrName "data-slot") "toast-progress-fill"
              , HP.attr (HH.AttrName "style") ("width: " <> show (toast.progress * 100.0) <> "%;")
              ]
              []
          ]
      ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action Slots Output m Unit
handleAction = case _ of
  Initialize ->
    pure unit

  DismissToastAction toastId -> do
    removeToast toastId
    H.raise (ToastDismissed toastId)

  HandleActionClick toastId actionId -> do
    H.raise (ToastActionClicked toastId actionId)
    removeToast toastId

  UpdateProgress toastId progress -> do
    H.modify_ \st -> st
      { toasts = map (\t -> if t.id == toastId then t { progress = progress } else t) st.toasts
      }

  AutoDismiss toastId -> do
    state <- H.get
    -- Find the toast and check if it should be dismissed
    let mToast = state.toasts !! (fromMaybe (-1) (findIndex (\t -> t.id == toastId) state.toasts))
    case mToast of
      Just toast | not toast.persistent -> do
        removeToast toastId
        H.raise (ToastDismissed toastId)
      _ -> pure unit

  Receive newInput ->
    H.modify_ _ { input = newInput }

-- Helper to remove a toast
removeToast :: forall m. MonadAff m => String -> H.HalogenM State Action Slots Output m Unit
removeToast toastId = do
  state <- H.get
  let mIdx = findIndex (\t -> t.id == toastId) state.toasts
  case mIdx of
    Just idx -> do
      let newToasts = fromMaybe state.toasts (deleteAt idx state.toasts)
      H.modify_ _ { toasts = newToasts }
    Nothing -> pure unit

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERIES
-- ═══════════════════════════════════════════════════════════════════════════════

handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action Slots Output m (Maybe a)
handleQuery = case _ of
  ShowToast config a -> do
    state <- H.get
    -- Generate unique ID if not provided
    let toastId = if config.id == "" then "toast-" <> show state.nextId else config.id
        newToast = config { id = toastId }
    -- Add toast (respecting max limit)
    H.modify_ \st -> 
      let toasts' = if length st.toasts >= st.input.maxToasts
                    then fromMaybe st.toasts (deleteAt 0 st.toasts)
                    else st.toasts
      in st { toasts = snoc toasts' newToast, nextId = st.nextId + 1 }
    -- Schedule auto-dismiss if not persistent
    when (not config.persistent && config.duration > 0) do
      void $ H.fork do
        liftAff $ delay (Milliseconds (toNumber config.duration))
        handleAction (AutoDismiss toastId)
    pure (Just a)

  DismissToast toastId a -> do
    removeToast toastId
    H.raise (ToastDismissed toastId)
    pure (Just a)

  DismissAll a -> do
    state <- H.get
    H.modify_ _ { toasts = [] }
    -- Raise events for all dismissed toasts
    for_ state.toasts \toast -> H.raise (ToastDismissed toast.id)
    pure (Just a)

  GetActiveToasts reply -> do
    state <- H.get
    pure (Just (reply (map _.id state.toasts)))

-- Helper for array length
length :: forall a. Array a -> Int
length arr = lengthImpl arr

foreign import lengthImpl :: forall a. Array a -> Int

-- Helper for for_
for_ :: forall m a. Monad m => Array a -> (a -> m Unit) -> m Unit
for_ [] _ = pure unit
for_ arr f = case arr !! 0 of
  Nothing -> pure unit
  Just x -> do
    f x
    for_ (fromMaybe [] (deleteAt 0 arr)) f

-- ═══════════════════════════════════════════════════════════════════════════════
-- MINIMAL FFI
-- ═══════════════════════════════════════════════════════════════════════════════
-- Only array length needed
