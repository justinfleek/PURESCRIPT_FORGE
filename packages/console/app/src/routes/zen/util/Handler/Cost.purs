-- | Omega Handler Cost Calculation
-- | Pure PureScript cost calculation logic
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/handler.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.Util.Handler.Cost
  ( calculateCost
  , CostBreakdown
  ) where

module Console.App.Routes.Omega.Util.Handler.Cost
  ( calculateCost
  , CostBreakdown
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe)
import Console.App.Routes.Omega.Util.Provider.Provider (UsageInfo)
import Console.App.Routes.Omega.Util.Handler.Types (ModelInfo, CostInfo)
import Console.Core.Util.Price (MicroCents, centsToMicroCents)

-- | Cost breakdown for logging
type CostBreakdown =
  { inputCost :: Int  -- in cents
  , outputCost :: Int
  , reasoningCost :: Maybe Int
  , cacheReadCost :: Maybe Int
  , cacheWrite5mCost :: Maybe Int
  , cacheWrite1hCost :: Maybe Int
  , totalCost :: Int  -- in cents
  }

-- | Calculate cost from usage info
calculateCost ::
  ModelInfo ->
  UsageInfo ->
  CostInfo
calculateCost modelInfo usageInfo =
  let
    -- Determine which cost model to use (200K threshold or standard)
    modelCost = if shouldUse200KCost modelInfo usageInfo
      then fromMaybe modelInfo.cost modelInfo.cost200K
      else modelInfo.cost
    
    -- Calculate individual costs (in cents, per 1M tokens)
    inputCost = calculateInputCost modelCost usageInfo
    outputCost = calculateOutputCost modelCost usageInfo
    reasoningCost = calculateReasoningCost modelCost usageInfo
    cacheReadCost = calculateCacheReadCost modelCost usageInfo
    cacheWrite5mCost = calculateCacheWrite5mCost modelCost usageInfo
    cacheWrite1hCost = calculateCacheWrite1hCost modelCost usageInfo
    
    -- Total cost in cents
    totalCostInCents = inputCost + outputCost +
      (fromMaybe 0 reasoningCost) +
      (fromMaybe 0 cacheReadCost) +
      (fromMaybe 0 cacheWrite5mCost) +
      (fromMaybe 0 cacheWrite1hCost)
  in
    { costInMicroCents: centsToMicroCents totalCostInCents }

-- | Check if we should use 200K cost model
shouldUse200KCost :: ModelInfo -> UsageInfo -> Boolean
shouldUse200KCost modelInfo usageInfo =
  isJust modelInfo.cost200K &&
  (usageInfo.inputTokens +
   (fromMaybe 0 usageInfo.cacheReadTokens) +
   (fromMaybe 0 usageInfo.cacheWrite5mTokens) +
   (fromMaybe 0 usageInfo.cacheWrite1hTokens)) > 200_000

-- | Calculate input cost (in cents)
calculateInputCost ::
  { input :: Number } ->
  UsageInfo ->
  Int
calculateInputCost modelCost usageInfo =
  round $ modelCost.input * (toNumber usageInfo.inputTokens) / 1_000_000.0 * 100.0

-- | Calculate output cost (in cents)
calculateOutputCost ::
  { output :: Number } ->
  UsageInfo ->
  Int
calculateOutputCost modelCost usageInfo =
  round $ modelCost.output * (toNumber usageInfo.outputTokens) / 1_000_000.0 * 100.0

-- | Calculate reasoning cost (in cents)
calculateReasoningCost ::
  { output :: Number } ->
  UsageInfo ->
  Maybe Int
calculateReasoningCost modelCost usageInfo =
  map (\tokens ->
    round $ modelCost.output * (toNumber tokens) / 1_000_000.0 * 100.0
  ) usageInfo.reasoningTokens

-- | Calculate cache read cost (in cents)
calculateCacheReadCost ::
  { cacheRead :: Maybe Number } ->
  UsageInfo ->
  Maybe Int
calculateCacheReadCost modelCost usageInfo =
  case modelCost.cacheRead, usageInfo.cacheReadTokens of
    Just cost, Just tokens ->
      Just $ round $ cost * (toNumber tokens) / 1_000_000.0 * 100.0
    _, _ -> Nothing

-- | Calculate cache write 5m cost (in cents)
calculateCacheWrite5mCost ::
  { cacheWrite5m :: Maybe Number } ->
  UsageInfo ->
  Maybe Int
calculateCacheWrite5mCost modelCost usageInfo =
  case modelCost.cacheWrite5m, usageInfo.cacheWrite5mTokens of
    Just cost, Just tokens ->
      Just $ round $ cost * (toNumber tokens) / 1_000_000.0 * 100.0
    _, _ -> Nothing

-- | Calculate cache write 1h cost (in cents)
calculateCacheWrite1hCost ::
  { cacheWrite1h :: Maybe Number } ->
  UsageInfo ->
  Maybe Int
calculateCacheWrite1hCost modelCost usageInfo =
  case modelCost.cacheWrite1h, usageInfo.cacheWrite1hTokens of
    Just cost, Just tokens ->
      Just $ round $ cost * (toNumber tokens) / 1_000_000.0 * 100.0
    _, _ -> Nothing

-- | Helper: convert Int to Number
foreign import toNumber :: Int -> Number

-- | Helper: convert Number to Int (round)
foreign import round :: Number -> Int
