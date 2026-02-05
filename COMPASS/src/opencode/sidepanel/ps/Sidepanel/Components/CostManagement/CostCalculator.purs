{-|
Module      : Sidepanel.Components.CostManagement.CostCalculator
Description : Calculate costs from token usage
Calculates costs from token usage based on model pricing.
-}
module Sidepanel.Components.CostManagement.CostCalculator where

import Prelude

import Data.Maybe (Maybe(..))
import Opencode.Provider.Provider (Model, ModelCost)
import Sidepanel.Components.CostManagement.CostManagementTypes
  ( TokenUsage
  , CostCalculation
  )

-- | Calculate cost from token usage
calculateCost :: Model -> TokenUsage -> CostCalculation
calculateCost model usage =
  let cost = model.cost
      -- Cost per 1M tokens, so divide by 1,000,000
      inputCost = (Number.fromInt usage.promptTokens / 1000000.0) * cost.input
      outputCost = (Number.fromInt usage.completionTokens / 1000000.0) * cost.output
      cacheReadCost = (Number.fromInt usage.cacheReadTokens / 1000000.0) * cost.cache.read
      cacheWriteCost = (Number.fromInt usage.cacheWriteTokens / 1000000.0) * cost.cache.write
      cacheCost = cacheReadCost + cacheWriteCost
      totalCost = inputCost + outputCost + cacheCost
  in
    { inputCost: inputCost
    , outputCost: outputCost
    , cacheCost: cacheCost
    , totalCost: totalCost
    , currency: "USD"  -- Default, would be configurable
    }

-- | Import Number utilities
import Data.Number as Number

-- | Project cost from estimated tokens
projectCost :: Model -> TokenUsage -> CostCalculation
projectCost model estimatedUsage = calculateCost model estimatedUsage

-- | Estimate tokens from content length (rough estimate)
estimateTokens :: String -> TokenUsage
estimateTokens content =
  -- Rough estimate: ~4 characters per token for code
  -- This is a simplification - would use proper tokenizer
  let charCount = Number.fromInt (String.length content)
      estimatedTokens = charCount / 4.0
      estimatedTokensInt = Number.floor estimatedTokens
      -- For completions, assume 50% prompt, 50% completion
      promptEstimate = estimatedTokensInt / 2
      completionEstimate = estimatedTokensInt / 2
  in
    { promptTokens: promptEstimate
    , completionTokens: completionEstimate
    , totalTokens: estimatedTokensInt
    , cacheReadTokens: 0
    , cacheWriteTokens: 0
    }

-- | Import Number utilities
import Data.Number as Number

-- | Estimate tokens for completion request
estimateCompletionTokens :: String -> Int -> TokenUsage
estimateCompletionTokens prompt maxTokens =
  let promptEstimate = estimateTokens prompt
  in
    { promptTokens: promptEstimate.promptTokens
    , completionTokens: maxTokens
    , totalTokens: promptEstimate.promptTokens + maxTokens
    , cacheReadTokens: 0
    , cacheWriteTokens: 0
    }
