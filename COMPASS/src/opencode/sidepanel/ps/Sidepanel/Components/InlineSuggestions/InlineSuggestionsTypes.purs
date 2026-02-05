{-|
Module      : Sidepanel.Components.InlineSuggestions.InlineSuggestionsTypes
Description : Types for inline code suggestions system
Core types for real-time inline code suggestions (like GitHub Copilot).
-}
module Sidepanel.Components.InlineSuggestions.InlineSuggestionsTypes where

import Prelude

-- | Position in editor
type Position =
  { line :: Int
  , column :: Int
  }

-- | Range in editor
type Range =
  { start :: Position
  , end :: Position
  }

-- | Inline code suggestion
type InlineSuggestion =
  { text :: String
  , range :: Range
  , confidence :: Number  -- 0.0 to 1.0
  , alternatives :: Array String  -- Alternative suggestions
  , completionKind :: CompletionKind
  }

-- | Type of completion
data CompletionKind
  = FunctionCompletion
  | VariableCompletion
  | TypeCompletion
  | ImportCompletion
  | SnippetCompletion

derive instance eqCompletionKind :: Eq CompletionKind

-- | Editor state snapshot
type EditorState =
  { filePath :: String
  , content :: String
  , cursorPosition :: Position
  , selection :: Maybe Range
  , language :: String
  , recentChanges :: Array FileChange
  }

-- | File change
type FileChange =
  { filePath :: String
  , changeType :: ChangeType
  , range :: Range
  , oldText :: String
  , newText :: String
  }

-- | Change type
data ChangeType
  = Insertion
  | Deletion
  | Replacement

derive instance eqChangeType :: Eq ChangeType

-- | Suggestion context
type SuggestionContext =
  { currentFile :: EditorState
  , prefix :: String  -- Text before cursor on current line
  , suffix :: String  -- Text after cursor on current line
  , imports :: Array Import
  , relatedFiles :: Array String
  , projectContext :: ProjectContext
  }

-- | Import statement
type Import =
  { module :: String
  , items :: Array String
  , qualified :: Boolean
  }

-- | Project context
type ProjectContext =
  { projectRoot :: String
  , dependencies :: Array String
  , recentFiles :: Array String
  , openFiles :: Array String
  }

-- | Suggestion stream
type SuggestionStream =
  { position :: Position
  , prefix :: String
  , suggestions :: Array InlineSuggestion
  , isComplete :: Boolean
  , streamId :: String
  }

-- | Suggestion request
type SuggestionRequest =
  { editorState :: EditorState
  , maxSuggestions :: Int
  , timeout :: Number  -- Milliseconds
  }

-- | Suggestion response
type SuggestionResponse =
  { suggestions :: Array InlineSuggestion
  , streamId :: String
  , latency :: Number  -- Milliseconds
  }
