-- | Help Overlay Component - Keyboard Shortcuts and Help Display
-- |
-- | **What:** Displays a modal overlay showing keyboard shortcuts and help information
-- |         organized by category (Navigation, Actions).
-- | **Why:** Improves discoverability of keyboard shortcuts and provides in-app help
-- |         without requiring external documentation.
-- | **How:** Renders a modal overlay with categorized shortcuts. Supports closing via
-- |         Escape key or close button. Visibility controlled by parent component.
-- |
-- | **Dependencies:** None (pure UI component)
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.HelpOverlay as HelpOverlay
-- |
-- | -- In parent component:
-- | HH.slot _help unit HelpOverlay.component
-- |   { visible: showHelp }
-- |   (case _ of
-- |     HelpOverlay.OverlayClosed -> HideHelp)
-- | ```
module Sidepanel.Components.HelpOverlay where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)

-- | Component state
type State =
  { visible :: Boolean
  }

-- | Component output
data Output
  = OverlayClosed

-- | Component input
type Input =
  { visible :: Boolean
  }

-- | Component
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: \{ visible } -> { visible }
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , receive = Just <<< Receive
      }
  }

-- | Actions
data Action
  = Receive Input
  | Close

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Receive input ->
    H.modify_ _ { visible = input.visible }
  
  Close ->
    H.raise OverlayClosed

-- | Render component
render :: forall m. State -> H.ComponentHTML Action () m
render state =
  if state.visible then
    HH.div
      [ HP.class_ (H.ClassName "help-overlay")
      , HE.onClick \_ -> Close
      ]
      [ HH.div
          [ HP.class_ (H.ClassName "help-overlay__content")
          , HE.onClick \_ -> pure unit
          ]
          [ HH.div
              [ HP.class_ (H.ClassName "help-overlay__header") ]
              [ HH.h2
                  [ HP.class_ (H.ClassName "help-overlay__title") ]
                  [ HH.text "Keyboard Shortcuts" ]
              , HH.button
                  [ HP.class_ (H.ClassName "help-overlay__close")
                  , HE.onClick \_ -> Close
                  ]
                  [ HH.text "×" ]
              ]
          , HH.div
              [ HP.class_ (H.ClassName "help-overlay__body") ]
              [ renderShortcuts
              ]
          ]
      ]
  else
    HH.text ""

-- | Render keyboard shortcuts
renderShortcuts :: forall m. H.ComponentHTML Action () m
renderShortcuts =
  HH.div
    [ HP.class_ (H.ClassName "shortcuts") ]
    [ renderSection "Navigation"
        [ renderShortcut "1-5" "Navigate to panels (Dashboard, Session, Proof, Timeline, Settings)"
        , renderShortcut "j/k" "Move down/up (Vim mode)"
        , renderShortcut "h/l" "Move left/right (Vim mode)"
        ]
    , renderSection "Actions"
        [ renderShortcut "Ctrl+Z" "Undo"
        , renderShortcut "Ctrl+Shift+Z" "Redo"
        , renderShortcut "Ctrl+Shift+P" "Open command palette"
        , renderShortcut "r" "Refresh current view"
        , renderShortcut "?" "Show this help"
        , renderShortcut "Escape" "Cancel/Close"
        , renderShortcut "Enter" "Confirm"
        ]
    ]

-- | Render a section of shortcuts
renderSection :: forall m. String -> Array (H.ComponentHTML Action () m) -> H.ComponentHTML Action () m
renderSection title shortcuts =
  HH.div
    [ HP.class_ (H.ClassName "shortcuts__section") ]
    [ HH.h3
        [ HP.class_ (H.ClassName "shortcuts__section-title") ]
        [ HH.text title ]
    , HH.ul
        [ HP.class_ (H.ClassName "shortcuts__list") ]
        shortcuts
    ]

-- | Render a single shortcut
renderShortcut :: forall m. String -> String -> H.ComponentHTML Action () m
renderShortcut keys description =
  HH.li
    [ HP.class_ (H.ClassName "shortcut") ]
    [ HH.span
        [ HP.class_ (H.ClassName "shortcut__keys") ]
        [ HH.text keys ]
    , HH.span
        [ HP.class_ (H.ClassName "shortcut__description") ]
        [ HH.text description ]
    ]
