{-|
Module      : Sidepanel.Components.InlineSuggestions.SuggestionEngine
Description : Core suggestion engine for inline code completions
Main engine that queries AI model and generates inline code suggestions.
-}
module Sidepanel.Components.InlineSuggestions.SuggestionEngine where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Effect (unsafePerformEffect)
import Sidepanel.Components.InlineSuggestions.InlineSuggestionsTypes
  ( SuggestionContext
  , InlineSuggestion
  , SuggestionRequest
  , SuggestionResponse
  , CompletionKind(..)
  , Range
  , Position
  , EditorState
  )
import Sidepanel.Components.InlineSuggestions.ContextBuilder (buildSuggestionContext)
import Sidepanel.Components.InlineSuggestions.ProviderIntegration
  ( ProviderIntegrationState
  , generateSuggestionsWithProvider
  )

-- | Query AI model for suggestions
querySuggestions :: Maybe ProviderIntegrationState -> SuggestionRequest -> Aff SuggestionResponse
querySuggestions providerStateM request = do
  -- Build context
  context <- buildSuggestionContext request.editorState
  
  -- Query model using ProviderIntegration if available
  suggestions <- case providerStateM of
    Nothing -> pure []  -- No provider available
    Just providerState -> generateSuggestionsWithProvider providerState context request.editorState.cursorPosition
  
  -- Filter and rank
  let filtered = filterSuggestions suggestions
  let ranked = rankSuggestions filtered
  
  pure
    { suggestions: Array.take request.maxSuggestions ranked
    , streamId: generateStreamId
    , latency: 0.0  -- Would measure actual latency
    }

-- | Generate suggestions from context using Provider integration
generateSuggestions :: Maybe ProviderIntegrationState -> SuggestionContext -> EditorState -> Aff (Array InlineSuggestion)
generateSuggestions providerStateM context editorState = do
  case providerStateM of
    Nothing -> pure []
    Just providerState -> generateSuggestionsWithProvider providerState context editorState.cursorPosition

-- | Filter suggestions (remove duplicates, low confidence, etc.)
filterSuggestions :: Array InlineSuggestion -> Array InlineSuggestion
filterSuggestions suggestions = do
  Array.filter (\s -> s.confidence > 0.3) suggestions

-- | Rank suggestions by relevance
rankSuggestions :: Array InlineSuggestion -> Array InlineSuggestion
rankSuggestions suggestions = do
  -- Sort by confidence descending
  Array.sortBy (\a b -> compare b.confidence a.confidence) suggestions

-- | Generate unique stream ID
generateStreamId :: String
generateStreamId = "stream-" <> show (unsafePerformEffect $ nowMillis)  -- Would use proper UUID

-- | Get current time in milliseconds
foreign import nowMillis :: Effect Number

-- | Import EditorState
import Sidepanel.Components.InlineSuggestions.InlineSuggestionsTypes (EditorState)
