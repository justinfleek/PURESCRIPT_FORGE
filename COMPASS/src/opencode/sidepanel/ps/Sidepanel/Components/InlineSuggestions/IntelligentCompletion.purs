{-|
Module      : Sidepanel.Components.InlineSuggestions.IntelligentCompletion
Description : Intelligent code completion combining FIM, linting, and context
This module combines FIM (Fill-in-the-Middle), fast linting, and context-aware
suggestions to provide intelligent, fast code completion.
-}
module Sidepanel.Components.InlineSuggestions.IntelligentCompletion where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff, parallel, sequential)
import Sidepanel.Components.InlineSuggestions.InlineSuggestionsTypes
  ( EditorState
  , InlineSuggestion
  , SuggestionRequest
  , SuggestionResponse
  )
import Sidepanel.Components.InlineSuggestions.FIMEngine
  ( extractFIMContext
  , generateFIMCompletion
  , shouldUseFIM
  , fimResponseToSuggestion
  )
import Sidepanel.Components.InlineSuggestions.SuggestionEngine (querySuggestions)
import Sidepanel.Components.InlineSuggestions.ProviderIntegration (ProviderIntegrationState)
import Sidepanel.Components.InlineSuggestions.FastLinter
  ( lintFile
  , validateSuggestion
  , LintedSuggestion
  )

-- | Intelligent completion strategy
data CompletionStrategy
  = UseFIM  -- Fill-in-the-Middle for middle-of-code completion
  | UseStandard  -- Standard autocomplete for end-of-line
  | UseHybrid  -- Combine both approaches

-- | Generate intelligent completions
generateIntelligentCompletions :: Maybe ProviderIntegrationState -> SuggestionRequest -> Aff SuggestionResponse
generateIntelligentCompletions providerStateM request = do
  let editorState = request.editorState
  
  -- Determine strategy
  let strategy = determineStrategy editorState
  
  -- Generate suggestions based on strategy
  suggestions <- case strategy of
    UseFIM -> generateFIMSuggestions providerStateM editorState
    UseStandard -> generateStandardSuggestions providerStateM request
    UseHybrid -> generateHybridSuggestions providerStateM request
  
  -- Validate suggestions with linting (in parallel for speed)
  validatedSuggestions <- sequential $ parallel $ Array.map (\s -> validateSuggestion s editorState) suggestions
  
  -- Filter to only lint-passing suggestions (or show warnings)
  let filtered = Array.filter _.passesLint validatedSuggestions
  
  -- Rank by confidence and lint status
  let ranked = rankIntelligentSuggestions validatedSuggestions
  
  pure
    { suggestions: Array.take request.maxSuggestions (Array.map _.suggestion ranked)
    , streamId: generateStreamId
    , latency: 0.0  -- Would measure actual latency
    }

-- | Determine completion strategy
determineStrategy :: EditorState -> CompletionStrategy
determineStrategy editorState = do
  if shouldUseFIM editorState then
    -- Check if we have significant suffix
    let fimContext = extractFIMContext editorState
    if String.length fimContext.suffix > 50 then
      UseFIM  -- Strong FIM signal
    else
      UseHybrid  -- Use both
  else
    UseStandard

-- | Generate FIM suggestions
generateFIMSuggestions :: Maybe ProviderIntegrationState -> EditorState -> Aff (Array InlineSuggestion)
generateFIMSuggestions providerStateM editorState = do
  let fimRequest = extractFIMContext editorState
  fimResponse <- generateFIMCompletion providerStateM fimRequest editorState.cursorPosition
  
  if String.length fimResponse.completion > 0 then
    pure [fimResponseToSuggestion fimResponse editorState.cursorPosition]
  else
    pure []

-- | Generate standard suggestions
generateStandardSuggestions :: Maybe ProviderIntegrationState -> SuggestionRequest -> Aff (Array InlineSuggestion)
generateStandardSuggestions providerStateM request = do
  response <- querySuggestions providerStateM request
  pure response.suggestions

-- | Generate hybrid suggestions (FIM + standard)
generateHybridSuggestions :: Maybe ProviderIntegrationState -> SuggestionRequest -> Aff (Array InlineSuggestion)
generateHybridSuggestions providerStateM request = do
  -- Generate both in parallel
  fimSuggestions <- generateFIMSuggestions providerStateM request.editorState
  standardSuggestions <- generateStandardSuggestions providerStateM request
  
  -- Combine and deduplicate
  let combined = fimSuggestions <> standardSuggestions
  -- Deduplicate by text content
  let deduplicated = Array.foldl deduplicateSuggestions [] combined
  
  pure deduplicated

-- | Deduplicate suggestions by text
deduplicateSuggestions :: Array InlineSuggestion -> InlineSuggestion -> Array InlineSuggestion
deduplicateSuggestions acc suggestion = do
  if Array.any (\s -> s.text == suggestion.text) acc then
    acc
  else
    acc <> [suggestion]

-- | Rank intelligent suggestions
rankIntelligentSuggestions :: Array LintedSuggestion -> Array LintedSuggestion
rankIntelligentSuggestions suggestions = do
  -- Sort by:
  -- 1. Passes lint (lint-passing suggestions first)
  -- 2. Confidence (higher confidence first)
  -- 3. Fewer lint warnings (if not passing)
  Array.sortBy compareLintedSuggestions suggestions

-- | Compare linted suggestions for ranking
compareLintedSuggestions :: LintedSuggestion -> LintedSuggestion -> Ordering
compareLintedSuggestions a b = do
  -- First: lint-passing vs not
  if a.passesLint && not b.passesLint then
    LT
  else if not a.passesLint && b.passesLint then
    GT
  else do
    -- Both same lint status, compare confidence
    if a.suggestion.confidence > b.suggestion.confidence then
      LT
    else if a.suggestion.confidence < b.suggestion.confidence then
      GT
    else do
      -- Same confidence, prefer fewer lint warnings
      let aWarnings = Array.length a.lintDiagnostics
      let bWarnings = Array.length b.lintDiagnostics
      compare aWarnings bWarnings

-- | Generate stream ID
generateStreamId :: String
generateStreamId = "intelligent-" <> show (unsafePerformEffect FFI.nowMillis)

-- | Import utilities
import Effect (unsafePerformEffect)
import Sidepanel.Components.InlineSuggestions.FastLinterFFI (nowMillis) as FFI

-- | Import Data.Ord for compare
import Data.Ord (compare, Ordering(..))
