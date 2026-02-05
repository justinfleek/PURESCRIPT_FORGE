{-|
Module      : Sidepanel.Components.InlineSuggestions.EditorIntegration
Description : Editor integration for inline code suggestions
Tracks editor state, cursor position, file changes, and triggers suggestions.
-}
module Sidepanel.Components.InlineSuggestions.EditorIntegration where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Effect.Aff (Aff, delay, Milliseconds(..))
import Effect.Class (liftEffect)
import Sidepanel.Components.InlineSuggestions.InlineSuggestionsTypes
  ( EditorState
  , InlineSuggestion
  , Position
  , SuggestionRequest
  )
import Sidepanel.Components.InlineSuggestions.IntelligentCompletion (generateIntelligentCompletions)

-- | Editor change event
type EditorChangeEvent =
  { filePath :: String
  , content :: String
  , cursorPosition :: Position
  , changeType :: ChangeType
  , timestamp :: Number
  }

-- | Change type
data ChangeType
  = Insertion
  | Deletion
  | CursorMove
  | FileOpen
  | FileSave

derive instance eqChangeType :: Eq ChangeType

-- | Editor watcher state
type EditorWatcherState =
  { currentState :: Maybe EditorState
  , pendingChanges :: Array EditorChangeEvent
  , suggestionDebounceTimer :: Maybe Int
  , lastSuggestionTime :: Number
  }

-- | Watch editor for changes and trigger suggestions
watchEditor :: (EditorState -> Aff (Array InlineSuggestion)) -> Aff Unit
watchEditor suggestionCallback = do
  -- This would set up editor event listeners
  -- For now, placeholder - would integrate with actual editor
  pure unit

-- | Handle editor change
handleEditorChange :: EditorChangeEvent -> EditorWatcherState -> Aff EditorWatcherState
handleEditorChange event state = do
  -- Update editor state
  let newState = updateEditorState event state.currentState
  
  -- Debounce suggestion requests (wait for user to stop typing)
  let debouncedState = debounceSuggestionRequest state event
  
  -- Trigger suggestion after debounce
  case debouncedState.suggestionDebounceTimer of
    Nothing -> do
      -- Request suggestions immediately
      suggestions <- generateIntelligentCompletions
        { editorState: fromMaybe (createEmptyState event.filePath) newState
        , maxSuggestions: 3
        , timeout: 2000.0
        }
      pure debouncedState
    Just _ -> pure debouncedState

-- | Update editor state from change event
updateEditorState :: EditorChangeEvent -> Maybe EditorState -> Maybe EditorState
updateEditorState event currentState = do
  Just
    { filePath: event.filePath
    , content: event.content
    , cursorPosition: event.cursorPosition
    , selection: Nothing  -- Would track selection
    , language: detectLanguage event.filePath
    , recentChanges: []  -- Would track recent changes
    }

-- | Create empty editor state
createEmptyState :: String -> EditorState
createEmptyState filePath =
  { filePath: filePath
  , content: ""
  , cursorPosition: { line: 0, column: 0 }
  , selection: Nothing
  , language: detectLanguage filePath
  , recentChanges: []
  }

-- | Detect language from file path
detectLanguage :: String -> String
detectLanguage filePath = do
  if String.contains (String.Pattern ".ts") filePath then
    "typescript"
  else if String.contains (String.Pattern ".js") filePath then
    "javascript"
  else if String.contains (String.Pattern ".purs") filePath then
    "purescript"
  else if String.contains (String.Pattern ".hs") filePath then
    "haskell"
  else if String.contains (String.Pattern ".lean") filePath then
    "lean4"
  else if String.contains (String.Pattern ".py") filePath then
    "python"
  else
    "unknown"

-- | Debounce suggestion requests
debounceSuggestionRequest :: EditorWatcherState -> EditorChangeEvent -> EditorWatcherState
debounceSuggestionRequest state event = do
  -- Clear existing timer
  let clearedTimer = Nothing  -- Would clear timeout
  
  -- Set new timer (300ms debounce)
  let newTimer = Just 0  -- Would set timeout ID
  
  state
    { pendingChanges = state.pendingChanges <> [event]
    , suggestionDebounceTimer = newTimer
    }

-- | Get current editor state (would read from actual editor)
getCurrentEditorState :: Aff (Maybe EditorState)
getCurrentEditorState = do
  -- This would read from the actual editor (Monaco, CodeMirror, etc.)
  -- For now, return Nothing
  pure Nothing

-- | Track cursor position changes
trackCursorPosition :: Position -> Aff Unit
trackCursorPosition position = do
  -- This would update cursor tracking
  -- Would trigger suggestions if position changed significantly
  pure unit

-- | Import fromMaybe
import Data.Maybe (fromMaybe)
