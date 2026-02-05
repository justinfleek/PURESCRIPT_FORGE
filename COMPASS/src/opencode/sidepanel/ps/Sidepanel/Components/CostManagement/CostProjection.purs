{-|
Module      : Sidepanel.Components.CostManagement.CostProjection
Description : Project costs before execution
Projects estimated costs before executing operations.
-}
module Sidepanel.Components.CostManagement.CostProjection where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Sidepanel.Components.CostManagement.CostManagementTypes
  ( CostProjection
  , TokenUsage
  , OperationType
  )
import Sidepanel.Components.CostManagement.CostCalculator (projectCost, estimateCompletionTokens)
import Opencode.Provider.Provider (Model)

-- | Project cost for inline suggestion
projectInlineSuggestionCost
  :: Model
  -> String  -- Context/prompt
  -> Int  -- Max tokens
  -> Aff CostProjection
projectInlineSuggestionCost model prompt maxTokens = do
  let estimatedUsage = estimateCompletionTokens prompt maxTokens
  let cost = projectCost model estimatedUsage
  
  -- Confidence based on prompt length and model
  let confidence = calculateConfidence prompt maxTokens
  
  pure
    { estimatedTokens: estimatedUsage
    , estimatedCost: cost.totalCost
    , confidence: confidence
    , modelId: model.id
    , operation: InlineSuggestion
    }

-- | Project cost for code review
projectCodeReviewCost
  :: Model
  -> String  -- Code content
  -> Aff CostProjection
projectCodeReviewCost model content = do
  let estimatedUsage = estimateTokens content
  let cost = projectCost model estimatedUsage
  
  pure
    { estimatedTokens: estimatedUsage
    , estimatedCost: cost.totalCost
    , confidence: 0.7  -- Code review is more predictable
    , modelId: model.id
    , operation: CodeReview
    }

-- | Project cost for refactoring
projectRefactoringCost
  :: Model
  -> String  -- Code to refactor
  -> Aff CostProjection
projectRefactoringCost model code = do
  let estimatedUsage = estimateTokens code
  let cost = projectCost model estimatedUsage
  
  pure
    { estimatedTokens: estimatedUsage
    , estimatedCost: cost.totalCost
    , confidence: 0.6  -- Refactoring varies more
    , modelId: model.id
    , operation: Refactoring
    }

-- | Project cost for test generation
projectTestGenerationCost
  :: Model
  -> String  -- Code to test
  -> Aff CostProjection
projectTestGenerationCost model code = do
  let estimatedUsage = estimateTokens code
  let cost = projectCost model estimatedUsage
  
  pure
    { estimatedTokens: estimatedUsage
    , estimatedCost: cost.totalCost
    , confidence: 0.7
    , modelId: model.id
    , operation: TestGeneration
    }

-- | Calculate confidence in projection
calculateConfidence :: String -> Int -> Number
calculateConfidence prompt maxTokens =
  -- Longer prompts = higher confidence
  -- Shorter maxTokens = higher confidence
  let promptLength = String.length prompt
      lengthConfidence = if promptLength > 1000 then 0.9 else if promptLength > 500 then 0.7 else 0.5
      tokenConfidence = if maxTokens < 500 then 0.9 else if maxTokens < 1000 then 0.7 else 0.5
  in
    (lengthConfidence + tokenConfidence) / 2.0

-- | Estimate tokens from content
estimateTokens :: String -> TokenUsage
estimateTokens content =
  let charCount = String.length content
      estimatedTokens = charCount / 4
  in
    { promptTokens: estimatedTokens
    , completionTokens: estimatedTokens  -- Assume similar completion size
    , totalTokens: estimatedTokens * 2
    , cacheReadTokens: 0
    , cacheWriteTokens: 0
    }

-- | Import types
import Sidepanel.Components.CostManagement.CostManagementTypes (OperationType(..))
