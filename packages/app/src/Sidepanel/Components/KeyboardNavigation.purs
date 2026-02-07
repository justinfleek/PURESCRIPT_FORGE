-- | Keyboard Navigation Component - Global Keyboard Shortcut Handler
-- |
-- | **What:** Provides global keyboard navigation and shortcuts for the application,
-- |         including Vim-style navigation (j/k/h/l), route navigation (1-5), command palette
-- |         (Ctrl+Shift+P), and action shortcuts (r, ?, Escape, Enter).
-- | **Why:** Enables efficient keyboard-driven navigation and actions, improving productivity
-- |         for power users. Supports both standard and Vim-style navigation modes.
-- | **How:** Attaches global keyboard event listeners to the document, parses keyboard
-- |         events to actions, and emits KeyboardActionTriggered output. Ignores shortcuts
-- |         when input elements are focused to avoid interfering with typing.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.Router`: Route types for navigation
-- |
-- | **Mathematical Foundation:**
-- | - **Input Focus Detection:** Shortcuts are ignored when input elements have focus to
-- |   prevent interference with typing.
-- | - **Vim Mode:** Vim-style navigation (j/k/h/l) only active when `vimMode` is enabled.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.KeyboardNavigation as KeyboardNav
-- |
-- | -- In parent component:
-- | HH.slot _keyboard unit KeyboardNav.component unit
-- |   (case _ of
-- |     KeyboardNav.KeyboardActionTriggered action -> HandleKeyboardAction action)
-- | ```
-- |
-- | Based on spec 48-KEYBOARD-NAVIGATION.md
module Sidepanel.Components.KeyboardNavigation where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Effect (Effect)
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Data.Maybe (Maybe(..))
import Web.Event.Event (EventType(..))
import Web.Event.EventTarget (addEventListener, eventListener, removeEventListener)
import Web.HTML (window)
import Web.HTML.Window (document)
import Web.DOM.Document (toEventTarget)
import Web.UIEvent.KeyboardEvent (KeyboardEvent, fromEvent, key, ctrlKey, shiftKey, altKey)
import Sidepanel.Router (Route(..))
import Data.Foldable (for_)
import Effect.Aff (error, killFiber, Fiber)
import Effect.Aff as Aff

-- | Keyboard action
data KeyboardAction
  = OpenCommandPalette
  | NavigateToRoute Route
  | MoveDown
  | MoveUp
  | MoveLeft
  | MoveRight
  | Refresh
  | ShowHelp
  | Cancel
  | Confirm
  | Undo
  | Redo
  | OpenSearch
  | OpenGameSelection

-- | Component state
type State =
  { enabled :: Boolean
  , vimMode :: Boolean
  }

-- | Component output
data Output
  = KeyboardActionTriggered KeyboardAction

-- | Component input
type Input = Unit

-- | Component
component :: forall q m. MonadAff m => H.Component q Input Output m
component = H.mkComponent
  { initialState: const { enabled: true, vimMode: true }
  , render: const (HH.text "")
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

-- | Actions
data Action
  = Initialize
  | HandleKeyDown KeyboardEvent

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Subscribe to keyboard events using Halogen's subscription system
    void $ H.subscribe keyboardEventEmitter
  
  HandleKeyDown event -> do
    state <- H.get
    when state.enabled do
      case parseKeyboardAction event state.vimMode of
        Just action -> do
          liftEffect $ preventDefault event
          H.raise (KeyboardActionTriggered action)
        Nothing ->
          pure unit

-- | Keyboard event emitter - Subscribes to global keydown events
keyboardEventEmitter :: forall m. MonadAff m => H.Emitter m Action
keyboardEventEmitter = H.Emitter \emit -> do
  doc <- liftEffect $ document =<< window
  let target = toEventTarget doc
  
  keydownListener <- liftEffect $ eventListener \e -> do
    case fromEvent e of
      Just ke -> do
        -- Check if input is focused (don't intercept typing)
        inputFocused <- isInputFocused ke
        if inputFocused then
          pure unit
        else
          -- Emit HandleKeyDown action
          liftEffect $ emit (HandleKeyDown ke)
      Nothing ->
        pure unit
  
  liftEffect $ addEventListener (EventType "keydown") keydownListener false target
  
  -- Return cleanup function
  pure $ removeEventListener (EventType "keydown") keydownListener false target

-- | Parse keyboard event to action
parseKeyboardAction :: KeyboardEvent -> Boolean -> Maybe KeyboardAction
parseKeyboardAction event vimMode
  -- Undo/Redo (Ctrl+Z, Ctrl+Shift+Z)
  | ctrlKey event && not (shiftKey event) && key event == "z" = 
      Just Undo
  | ctrlKey event && shiftKey event && key event == "z" = 
      Just Redo
  
  -- Command palette (Ctrl+Shift+P)
  | ctrlKey event && shiftKey event && key event == "p" = 
      Just OpenCommandPalette
  
  -- Search (Ctrl+K or Ctrl+F)
  | ctrlKey event && not (shiftKey event) && (key event == "k" || key event == "f") = 
      Just OpenSearch
  
  -- Easter egg games (Ctrl+Shift+T for Tetris, Ctrl+Shift+P for Pong when not command palette)
  | ctrlKey event && shiftKey event && key event == "t" = 
      Just OpenGameSelection
  
  -- Vim-style navigation (only if vimMode enabled)
  | vimMode && key event == "j" = Just MoveDown
  | vimMode && key event == "k" = Just MoveUp
  | vimMode && key event == "h" = Just MoveLeft
  | vimMode && key event == "l" = Just MoveRight
  
  -- Route navigation (number keys)
  | key event == "1" = Just (NavigateToRoute Dashboard)
  | key event == "2" = Just (NavigateToRoute (Session Nothing))
  | key event == "3" = Just (NavigateToRoute Proof)
  | key event == "4" = Just (NavigateToRoute Timeline)
  | key event == "5" = Just (NavigateToRoute Settings)
  
  -- Actions
  | key event == "r" = Just Refresh
  | key event == "?" = Just ShowHelp
  | key event == "Escape" = Just Cancel
  | key event == "Enter" = Just Confirm
  
  | otherwise = Nothing

-- | Check if input element has focus
foreign import isInputFocused :: KeyboardEvent -> Effect Boolean

-- | Prevent default event behavior
foreign import preventDefault :: KeyboardEvent -> Effect Unit
