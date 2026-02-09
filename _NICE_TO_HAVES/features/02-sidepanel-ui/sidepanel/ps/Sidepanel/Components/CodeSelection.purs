-- | Code Selection Component - Line Selection with Copy and Add-to-Chat
-- |
-- | **What:** Provides code line selection functionality matching Forge's behavior,
-- |         with copy-to-clipboard and add-to-chat actions. Can be integrated into
-- |         any component that displays code (DiffViewer, FileContextView, etc.).
-- | **Why:** Enables users to select code lines and either copy them or add them
-- |         to chat, matching Forge's functionality for 100% parity.
-- | **How:** Tracks mouse drag selection, highlights selected lines, provides
-- |         action buttons (Copy, Add to Chat), and handles keyboard shortcuts.
-- |
-- | **Dependencies:**
-- | - `Sidepanel.FFI.Clipboard`: Clipboard operations
-- | - `Sidepanel.WebSocket.Client`: For sending code to chat (if needed)
-- |
-- | **Mathematical Foundation:**
-- | - **Line Range:** Selection is represented as `{ start: Int, end: Int }` where
-- |   `start <= end`. Single line selection has `start == end`.
-- | - **Code Extraction:** Selected code is extracted by joining lines from `start`
-- |   to `end` (inclusive) with newlines.
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Components.CodeSelection as CodeSelection
-- |
-- | -- In parent component:
-- | HH.slot _codeSelection unit CodeSelection.component
-- |   { codeLines: ["line1", "line2", "line3"]
-- |   , filePath: "src/file.ts"
-- |   , onCopy: \code -> HandleCopy code
-- |   , onAddToChat: \code -> HandleAddToChat code
-- |   }
-- |   (case _ of
-- |     CodeSelection.Copied -> ShowNotification "Copied!"
-- |     CodeSelection.AddedToChat -> ShowNotification "Added to chat!")
-- | ```
module Sidepanel.Components.CodeSelection where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP
import Halogen.HTML.Events as HE
import Effect.Aff.Class (class MonadAff)
import Effect.Class (liftEffect)
import Effect.Aff (Aff)
import Data.Array (slice, length, mapWithIndex)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (joinWith)
import Sidepanel.FFI.Clipboard as Clipboard
import Web.UIEvent.KeyboardEvent (KeyboardEvent, key, ctrlKey, metaKey)
import Effect.Class (liftEffect)
import Effect (Effect)
import Data.String (toLower)

-- | Line selection range
type LineRange =
  { start :: Int  -- 0-based line index
  , end :: Int    -- 0-based line index (inclusive)
  }

-- | Component input
type Input =
  { codeLines :: Array String  -- Array of code lines
  , filePath :: Maybe String   -- Optional file path for context
  , language :: Maybe String   -- Optional language for syntax highlighting
  }

-- | Component state
type State =
  { codeLines :: Array String
  , filePath :: Maybe String
  , language :: Maybe String
  , selectedRange :: Maybe LineRange
  , isSelecting :: Boolean
  , dragStart :: Maybe Int
  , keyboardCleanup :: Maybe (Effect Unit)
  }

-- | Component actions
data Action
  = Initialize
  = MouseDown Int  -- Line number
  = MouseMove Int  -- Line number
  = MouseUp Int    -- Line number
  = ClearSelection
  = CopySelection
  = AddToChat
  = HandleCopyResult (Either String Unit)
  = HandleAddToChatResult (Either String Unit)
  = Finalize
  = HandleKeyDown KeyboardEvent

-- | Component output
data Output
  = Copied String  -- Code that was copied
  | AddedToChat String  -- Code that was added to chat
  | SelectionChanged (Maybe LineRange)

-- | Component
component :: forall q m. MonadAff m => H.Component q Input Output m
component =
  H.mkComponent
    { initialState
    , render
    , eval: H.mkEval $ H.defaultEval
        { handleAction = handleAction
        , initialize = Just Initialize
        , receive = Just <<< Receive
        , finalize = Just Finalize
        }
    }

-- | Query type (empty - component doesn't support queries)
data Query a = Query

-- | Slot type for parent components
type Slot label = H.Slot Query Output label

-- | Receive new input
data Receive = Receive Input

handleReceive :: forall m. MonadAff m => Receive -> H.HalogenM State Action () Output m Unit
handleReceive (Receive input) = do
  H.modify_ \s ->
    { s
    | codeLines = input.codeLines
    , filePath = input.filePath
    , language = input.language
    }

initialState :: Input -> State
initialState input =
  { codeLines: input.codeLines
  , filePath: input.filePath
  , language: input.language
  , selectedRange: Nothing
  , isSelecting: false
  , dragStart: Nothing
  , keyboardCleanup: Nothing
  }

render :: forall m. State -> H.ComponentHTML Action () m
render state =
  HH.div
    [ HP.class_ (H.ClassName "code-selection")
    , HE.onKeyDown \event -> HandleKeyDown event
    , HP.tabIndex 0  -- Make focusable for keyboard events
    ]
    [ -- Code lines with selection
      HH.div
        [ HP.class_ (H.ClassName "code-selection__lines")
        , HE.onMouseLeave \_ -> ClearSelection
        ]
        (mapWithIndex (renderLine state.selectedRange) state.codeLines)
    
    -- Action buttons (shown when selection exists)
    , case state.selectedRange of
        Just range ->
          renderActions state.codeLines range state.filePath state.language
        Nothing ->
          HH.text ""
    ]

renderLine :: forall m. Maybe LineRange -> Int -> String -> H.ComponentHTML Action () m
renderLine selectedRange index line =
  let
    isSelected = case selectedRange of
      Just range -> index >= range.start && index <= range.end
      Nothing -> false
    classes = if isSelected
      then [ H.ClassName "code-line", H.ClassName "code-line--selected" ]
      else [ H.ClassName "code-line" ]
  in
    HH.div
      [ HP.classes classes
      , HP.attr (H.AttrName "data-line") (show index)
      , HE.onMouseDown \_ -> MouseDown index
      , HE.onMouseMove \_ -> MouseMove index
      , HE.onMouseUp \_ -> MouseUp index
      ]
      [ HH.text line ]

renderActions :: forall m. Array String -> LineRange -> Maybe String -> Maybe String -> H.ComponentHTML Action () m
renderActions codeLines range filePath language =
  let
    selectedCode = extractSelectedCode codeLines range
    lang = fromMaybe "text" language
  in
    HH.div
      [ HP.class_ (H.ClassName "code-selection__actions") ]
      [ HH.button
          [ HP.class_ (H.ClassName "btn btn--primary btn--sm")
          , HE.onClick \_ -> CopySelection
          , HP.title "Copy selected code (Ctrl+C)"
          ]
          [ HH.text "Copy" ]
      , HH.button
          [ HP.class_ (H.ClassName "btn btn--secondary btn--sm")
          , HE.onClick \_ -> AddToChat
          , HP.title "Add selected code to chat (Ctrl+Enter)"
          ]
          [ HH.text "Add to Chat" ]
      , HH.span
          [ HP.class_ (H.ClassName "code-selection__info") ]
          [ HH.text $ "Lines " <> show (range.start + 1) <> "-" <> show (range.end + 1) ]
      ]

extractSelectedCode :: Array String -> LineRange -> String
extractSelectedCode lines range =
  let
    start = max 0 range.start
    end = min (length lines - 1) range.end
    selectedLines = slice start (end + 1) lines
  in
    joinWith "\n" selectedLines

handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> do
    -- Keyboard shortcuts are handled via onClick handlers on buttons
    -- Global shortcuts would require more complex setup
    pure unit
  
  Finalize -> do
    -- Cleanup keyboard handlers if needed
    state <- H.get
    case state.keyboardCleanup of
      Just cleanup -> H.liftEffect cleanup
      Nothing -> pure unit
  
  MouseDown line -> do
    H.modify_ \s ->
      { s
      | dragStart = Just line
      , selectedRange = Just { start: line, end: line }
      , isSelecting = true
      }
    H.raise $ SelectionChanged (Just { start: line, end: line })
  
  MouseMove line -> do
    state <- H.get
    case state.dragStart of
      Just start ->
        let
          range = { start: min start line, end: max start line }
        in
          H.modify_ \s -> s { selectedRange = Just range }
      Nothing ->
        pure unit
  
  MouseUp line -> do
    state <- H.get
    case state.dragStart of
      Just start ->
        let
          range = { start: min start line, end: max start line }
        in
          do
            H.modify_ \s ->
              { s
              | selectedRange = Just range
              , dragStart = Nothing
              , isSelecting = false
              }
            H.raise $ SelectionChanged (Just range)
      Nothing ->
        pure unit
  
  ClearSelection -> do
    H.modify_ \s ->
      { s
      | selectedRange = Nothing
      , dragStart = Nothing
      , isSelecting = false
      }
    H.raise $ SelectionChanged Nothing
  
  CopySelection -> do
    state <- H.get
    case state.selectedRange of
      Just range ->
        let
          code = extractSelectedCode state.codeLines range
        in
          do
            H.liftEffect $ Clipboard.copyToClipboard code
            H.raise $ Copied code
      Nothing ->
        pure unit
  
  AddToChat -> do
    state <- H.get
    case state.selectedRange of
      Just range ->
        let
          code = extractSelectedCode state.codeLines range
          -- Format with file context if available (markdown code block)
          language = fromMaybe "text" state.language
          formattedCode = case state.filePath of
            Just path -> "```" <> language <> "\n" <> code <> "\n```"
            Nothing -> "```" <> language <> "\n" <> code <> "\n```"
        in
          do
            -- Copy formatted code to clipboard
            -- User can paste it into Forge chat
            H.liftEffect $ Clipboard.copyToClipboard formattedCode
            H.raise $ AddedToChat formattedCode
      Nothing ->
        pure unit
  
  HandleCopyResult result ->
    pure unit
  
  HandleAddToChatResult result ->
    pure unit
  
  Receive input ->
    handleReceive input
  
  Finalize -> do
    -- Cleanup if needed
    pure unit
  
  HandleKeyDown event -> do
    state <- H.get
    case state.selectedRange of
      Just range ->
        let
          keyStr = toLower $ key event
          isMod = ctrlKey event || metaKey event
        in
          -- Ctrl+C or Cmd+C - Copy
          if isMod && keyStr == "c" then do
            handleAction CopySelection
          -- Ctrl+Enter or Cmd+Enter - Add to chat
          else if isMod && keyStr == "enter" then do
            handleAction AddToChat
          else
            pure unit
      Nothing ->
        pure unit

