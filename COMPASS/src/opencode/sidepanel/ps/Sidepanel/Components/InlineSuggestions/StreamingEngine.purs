{-|
Module      : Sidepanel.Components.InlineSuggestions.StreamingEngine
Description : Streaming support for real-time suggestion updates

Handles streaming suggestions from AI model for real-time updates as user types.
-}
module Sidepanel.Components.InlineSuggestions.StreamingEngine where

import Prelude

import Data.Array as Array
import Effect.Aff (Aff, makeAff)
import Effect (Effect)
import Sidepanel.Components.InlineSuggestions.InlineSuggestionsTypes
  ( EditorState
  , InlineSuggestion
  , SuggestionRequest
  , SuggestionStream
  )

-- | Stream suggestion updates (full suggestions)
streamSuggestions :: Maybe ProviderIntegrationState -> SuggestionRequest -> (InlineSuggestion -> Effect Unit) -> Aff Unit
streamSuggestions providerStateM request onUpdate = do
  -- Generate suggestions using ProviderIntegration if available
  response <- generateIntelligentCompletions providerStateM request
  
  -- Emit each suggestion as it becomes available
  Array.for_ response.suggestions \suggestion -> do
    liftEffect $ onUpdate suggestion
  
  pure unit

-- | Stream suggestion chunks (for incremental text generation)
streamSuggestionChunks :: Maybe ProviderIntegrationState -> SuggestionRequest -> (String -> Aff Unit) -> Aff (Maybe String)
streamSuggestionChunks providerStateM request onChunk = do
  -- Generate stream ID
  let streamId = "stream-" <> show (unsafePerformEffect FFI.nowMillis)
  
  -- Use ProviderIntegration to stream chunks
  case providerStateM of
    Nothing -> pure (Just streamId)  -- Return stream ID even if no provider
    Just providerState -> do
      -- Build context for streaming
      context <- buildSuggestionContext request.editorState
      
      -- Stream using ProviderIntegration (runs in background)
      _ <- generateStreamingSuggestions providerState context request.editorState.cursorPosition onChunk
      
      pure (Just streamId)

-- | Cancel streaming
cancelStream :: String -> Effect Unit
cancelStream streamId = do
  -- This would cancel the streaming request
  -- Would abort fetch/websocket connection
  pure unit

-- | Import utilities
import Effect.Class (liftEffect)
import Effect (unsafePerformEffect)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Sidepanel.Components.InlineSuggestions.IntelligentCompletion (generateIntelligentCompletions)
import Sidepanel.Components.InlineSuggestions.ProviderIntegration (ProviderIntegrationState, generateStreamingSuggestions)
import Sidepanel.Components.InlineSuggestions.ContextBuilder (buildSuggestionContext)
import Sidepanel.Components.InlineSuggestions.InlineSuggestionsTypes (InlineSuggestion, Position)
import Data.Maybe (Maybe(..))
import Sidepanel.Components.InlineSuggestions.FastLinterFFI (nowMillis) as FFI
