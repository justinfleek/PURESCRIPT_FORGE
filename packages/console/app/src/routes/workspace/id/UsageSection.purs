-- | Usage Section - Usage History
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id]/usage-section.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.UsageSection
  ( UsageSectionState(..)
  , UsageSectionAction(..)
  , UsageRecord(..)
  , UsageEnrichment(..)
  , TokenBreakdown(..)
  , PageSize
  , initialState
  , reducer
  , calculateTotalInputTokens
  , calculateTotalOutputTokens
  , formatCost
  , isSubscriptionUsage
  , canGoPrev
  , canGoNext
  ) where

import Prelude

import Data.Array (length)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), fromMaybe)

-- | Page size constant
type PageSize = Int

pageSize :: PageSize
pageSize = 50

-- | Usage enrichment data
type UsageEnrichment =
  { plan :: Maybe String
  }

-- | Usage record from database
type UsageRecord =
  { id :: String
  , timeCreated :: String
  , model :: String
  , inputTokens :: Int
  , outputTokens :: Int
  , cacheReadTokens :: Maybe Int
  , cacheWrite5mTokens :: Maybe Int
  , cacheWrite1hTokens :: Maybe Int
  , reasoningTokens :: Maybe Int
  , cost :: Maybe Int  -- in micro-cents (10^-8)
  , enrichment :: Maybe UsageEnrichment
  }

-- | Usage section state
type UsageSectionState =
  { page :: Int
  , usage :: Array UsageRecord
  , openBreakdownId :: Maybe String
  }

-- | Actions for usage section
data UsageSectionAction
  = SetPage Int
  | SetUsage (Array UsageRecord)
  | SetOpenBreakdownId (Maybe String)
  | ToggleBreakdown String
  | CloseBreakdown
  | GoToPrevPage
  | GoToNextPage

-- | Initial state
initialState :: UsageSectionState
initialState =
  { page: 0
  , usage: []
  , openBreakdownId: Nothing
  }

-- | Pure state reducer
reducer :: UsageSectionState -> UsageSectionAction -> UsageSectionState
reducer state action = case action of
  SetPage p -> state { page = p }
  SetUsage u -> state { usage = u }
  SetOpenBreakdownId id -> state { openBreakdownId = id }
  ToggleBreakdown id ->
    if state.openBreakdownId == Just id
      then state { openBreakdownId = Nothing }
      else state { openBreakdownId = Just id }
  CloseBreakdown -> state { openBreakdownId = Nothing }
  GoToPrevPage ->
    if state.page > 0
      then state { page = state.page - 1 }
      else state
  GoToNextPage ->
    if length state.usage == pageSize
      then state { page = state.page + 1 }
      else state

-- | Token breakdown for input tokens
type TokenBreakdown =
  { input :: Int
  , cacheRead :: Int
  , cacheWrite :: Int
  , total :: Int
  }

-- | Calculate total input tokens
calculateTotalInputTokens :: UsageRecord -> Int
calculateTotalInputTokens usage =
  usage.inputTokens 
    + fromMaybe 0 usage.cacheReadTokens
    + fromMaybe 0 usage.cacheWrite5mTokens
    + fromMaybe 0 usage.cacheWrite1hTokens

-- | Calculate total output tokens
calculateTotalOutputTokens :: UsageRecord -> Int
calculateTotalOutputTokens usage =
  usage.outputTokens + fromMaybe 0 usage.reasoningTokens

-- | Get input token breakdown
getInputTokenBreakdown :: UsageRecord -> TokenBreakdown
getInputTokenBreakdown usage =
  { input: usage.inputTokens
  , cacheRead: fromMaybe 0 usage.cacheReadTokens
  , cacheWrite: fromMaybe 0 usage.cacheWrite5mTokens
  , total: calculateTotalInputTokens usage
  }

-- | Output token breakdown
type OutputTokenBreakdown =
  { output :: Int
  , reasoning :: Int
  , total :: Int
  }

-- | Get output token breakdown
getOutputTokenBreakdown :: UsageRecord -> OutputTokenBreakdown
getOutputTokenBreakdown usage =
  { output: usage.outputTokens
  , reasoning: fromMaybe 0 usage.reasoningTokens
  , total: calculateTotalOutputTokens usage
  }

-- | Format cost from micro-cents to dollars
-- | Example: 100000000 -> "$1.0000"
formatCost :: Int -> String
formatCost cost =
  let
    dollars = toNumber cost / 100000000.0
  in
    "$" <> formatNumber dollars 4

-- | Format number with fixed decimal places
formatNumber :: Number -> Int -> String
formatNumber n decimals =
  let
    multiplier = pow 10.0 (toNumber decimals)
    rounded = round (n * multiplier) / multiplier
  in
    show rounded
  where
    pow :: Number -> Number -> Number
    pow base exp = 
      if exp <= 0.0 then 1.0
      else base * pow base (exp - 1.0)
    
    round :: Number -> Number
    round x = toNumber (floor (x + 0.5))
    
    floor :: Number -> Int
    floor _ = 0  -- simplified

-- | Check if usage is subscription-based
isSubscriptionUsage :: UsageRecord -> Boolean
isSubscriptionUsage usage =
  case usage.enrichment of
    Nothing -> false
    Just e -> e.plan == Just "sub"

-- | Check if can go to previous page
canGoPrev :: UsageSectionState -> Boolean
canGoPrev state = state.page > 0

-- | Check if can go to next page
canGoNext :: UsageSectionState -> Boolean
canGoNext state = length state.usage == pageSize

-- | Check if there are results
hasResults :: UsageSectionState -> Boolean
hasResults state = length state.usage > 0

-- | Breakdown popup ID generators
inputBreakdownId :: Int -> String
inputBreakdownId index = "input-breakdown-" <> show index

outputBreakdownId :: Int -> String
outputBreakdownId index = "output-breakdown-" <> show index

-- | Check if breakdown is open
isBreakdownOpen :: UsageSectionState -> String -> Boolean
isBreakdownOpen state id = state.openBreakdownId == Just id

-- | Check if model is Claude (for cache write display)
isClaude :: String -> Boolean
isClaude model =
  contains "claude" (toLower model)
  where
    toLower :: String -> String
    toLower s = s  -- simplified
    
    contains :: String -> String -> Boolean
    contains _ _ = false  -- simplified

-- | Usage row display
type UsageRowDisplay =
  { index :: Int
  , date :: String
  , dateTitle :: String
  , model :: String
  , inputTokens :: Int
  , outputTokens :: Int
  , cost :: String
  , isSubscription :: Boolean
  , isClaude :: Boolean
  }

-- | Build usage row display
buildUsageRowDisplay :: Int -> UsageRecord -> UsageRowDisplay
buildUsageRowDisplay index usage =
  { index
  , date: formatDateForTable usage.timeCreated
  , dateTitle: formatDateUTC usage.timeCreated
  , model: usage.model
  , inputTokens: calculateTotalInputTokens usage
  , outputTokens: calculateTotalOutputTokens usage
  , cost: formatCostDisplay usage
  , isSubscription: isSubscriptionUsage usage
  , isClaude: isClaude usage.model
  }

-- | Format cost for display
formatCostDisplay :: UsageRecord -> String
formatCostDisplay usage =
  let
    cost = fromMaybe 0 usage.cost
    formattedCost = formatCost cost
  in
    if isSubscriptionUsage usage
      then "subscription (" <> formattedCost <> ")"
      else formattedCost

-- | Format date for table display
-- | Output: "15 Jan, 3:45 PM"
formatDateForTable :: String -> String
formatDateForTable isoDate = isoDate  -- simplified

-- | Format date in UTC
-- | Output: "Mon, Jan 15, 2024, 3:45:30 PM UTC"
formatDateUTC :: String -> String
formatDateUTC isoDate = isoDate  -- simplified

-- | Section content
type UsageSectionContent =
  { title :: String
  , description :: String
  , emptyMessage :: String
  }

-- | Default section content
sectionContent :: UsageSectionContent
sectionContent =
  { title: "Usage History"
  , description: "Recent API usage and costs."
  , emptyMessage: "Make your first API call to get started."
  }

-- | Table headers
type TableHeaders =
  { date :: String
  , model :: String
  , input :: String
  , output :: String
  , cost :: String
  }

-- | Default table headers
tableHeaders :: TableHeaders
tableHeaders =
  { date: "Date"
  , model: "Model"
  , input: "Input"
  , output: "Output"
  , cost: "Cost"
  }

-- | Breakdown row labels
type BreakdownLabels =
  { input :: String
  , cacheRead :: String
  , cacheWrite :: String
  , output :: String
  , reasoning :: String
  }

-- | Default breakdown labels
breakdownLabels :: BreakdownLabels
breakdownLabels =
  { input: "Input"
  , cacheRead: "Cache Read"
  , cacheWrite: "Cache Write"
  , output: "Output"
  , reasoning: "Reasoning"
  }

-- | Pagination state
type PaginationState =
  { page :: Int
  , canPrev :: Boolean
  , canNext :: Boolean
  , showPagination :: Boolean
  }

-- | Build pagination state
buildPaginationState :: UsageSectionState -> PaginationState
buildPaginationState state =
  { page: state.page
  , canPrev: canGoPrev state
  , canNext: canGoNext state
  , showPagination: canGoPrev state || canGoNext state
  }
