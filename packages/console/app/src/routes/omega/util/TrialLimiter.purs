-- | Omega Trial Limiter
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/trialLimiter.ts
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Omega.Util.TrialLimiter
  ( TrialConfig(..)
  , TrialLimit(..)
  , TrialState(..)
  , UsageInfo(..)
  , findLimit
  , isTrial
  , calculateUsage
  , isEnabled
  ) where

import Prelude

import Data.Array (filter)
import Data.Maybe (Maybe(..))

-- | Trial limit configuration
type TrialLimit =
  { client :: Maybe String   -- Client identifier (Nothing = default)
  , limit :: Int             -- Token limit
  }

-- | Trial configuration
type TrialConfig =
  { provider :: String
  , limits :: Array TrialLimit
  }

-- | Trial state
type TrialState =
  { ip :: String
  , currentUsage :: Int
  , isTrial :: Boolean
  }

-- | Usage info for tracking
type UsageInfo =
  { inputTokens :: Int
  , outputTokens :: Int
  , reasoningTokens :: Maybe Int
  , cacheReadTokens :: Maybe Int
  , cacheWrite5mTokens :: Maybe Int
  , cacheWrite1hTokens :: Maybe Int
  }

-- | Find applicable limit for client
findLimit :: Array TrialLimit -> String -> Maybe Int
findLimit limits client =
  case findExact limits client of
    Just limit -> Just limit.limit
    Nothing -> findDefault limits
  where
    findExact :: Array TrialLimit -> String -> Maybe TrialLimit
    findExact ls c = 
      case filter (\l -> l.client == Just c) ls of
        [l] -> Just l
        _ -> Nothing
    
    findDefault :: Array TrialLimit -> Maybe Int
    findDefault ls =
      case filter (\l -> l.client == Nothing) ls of
        [l] -> Just l.limit
        _ -> Nothing

-- | Check if usage qualifies as trial (under limit)
isTrial :: Int -> Int -> Boolean
isTrial currentUsage limit = currentUsage < limit

-- | Calculate total usage from usage info
calculateUsage :: UsageInfo -> Int
calculateUsage info =
  info.inputTokens +
  info.outputTokens +
  fromMaybe 0 info.reasoningTokens +
  fromMaybe 0 info.cacheReadTokens +
  fromMaybe 0 info.cacheWrite5mTokens +
  fromMaybe 0 info.cacheWrite1hTokens
  where
    fromMaybe :: Int -> Maybe Int -> Int
    fromMaybe default Nothing = default
    fromMaybe _ (Just x) = x

-- | Check if trial limiting is enabled
isEnabled :: Maybe TrialConfig -> String -> Boolean
isEnabled Nothing _ = false
isEnabled (Just _) "" = false  -- No IP = disabled
isEnabled (Just config) client =
  case findLimit config.limits client of
    Nothing -> false
    Just _ -> true

-- | Build initial trial state
buildTrialState :: String -> Int -> Int -> TrialState
buildTrialState ip currentUsage limit =
  { ip
  , currentUsage
  , isTrial: isTrial currentUsage limit
  }

-- | Update trial state after usage
updateTrialState :: TrialState -> UsageInfo -> TrialState
updateTrialState state usageInfo =
  let
    additionalUsage = calculateUsage usageInfo
  in
    state { currentUsage = state.currentUsage + additionalUsage }

-- | Build usage update for database
type TrialUsageUpdate =
  { ip :: String
  , usage :: Int
  }

-- | Build usage update
buildUsageUpdate :: String -> UsageInfo -> TrialUsageUpdate
buildUsageUpdate ip usageInfo =
  { ip
  , usage: calculateUsage usageInfo
  }
