-- | Black Section - Subscription Management
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id]/billing/black-section.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.Billing.BlackSection
  ( BlackSectionState(..)
  , BlackSectionAction(..)
  , SubscriptionInfo(..)
  , UsageAnalysis(..)
  , UsageFormData(..)
  , initialState
  , reducer
  , formatResetTime
  , analyzeRollingUsage
  , analyzeWeeklyUsage
  , buildUsageDisplay
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- | Usage analysis result
type UsageAnalysis =
  { usagePercent :: Int
  , resetInSec :: Int
  }

-- | Subscription info from database
type SubscriptionInfo =
  { plan :: Int                   -- monthly plan amount in dollars
  , useBalance :: Boolean
  , rollingUsage :: UsageAnalysis
  , weeklyUsage :: UsageAnalysis
  }

-- | Black section state
type BlackSectionState =
  { sessionRedirecting :: Boolean
  , cancelled :: Boolean
  , enrolled :: Boolean
  }

-- | Actions for black section
data BlackSectionAction
  = SetSessionRedirecting Boolean
  | SetCancelled Boolean
  | SetEnrolled Boolean

-- | Initial state
initialState :: BlackSectionState
initialState =
  { sessionRedirecting: false
  , cancelled: false
  , enrolled: false
  }

-- | Pure state reducer
reducer :: BlackSectionState -> BlackSectionAction -> BlackSectionState
reducer state action = case action of
  SetSessionRedirecting redirecting -> state { sessionRedirecting = redirecting }
  SetCancelled cancelled -> state { cancelled = cancelled }
  SetEnrolled enrolled -> state { enrolled = enrolled }

-- | Format reset time from seconds to human readable
-- | Examples:
-- |   86400 -> "1 day 0 hours"
-- |   90000 -> "1 day 1 hour"
-- |   3660 -> "1 hour 1 minute"
-- |   120 -> "2 minutes"
-- |   30 -> "a few seconds"
formatResetTime :: Int -> String
formatResetTime seconds
  | seconds >= 86400 =
      let
        days = seconds / 86400
        hours = (seconds `mod` 86400) / 3600
        dayLabel = if days == 1 then "day" else "days"
        hourLabel = if hours == 1 then "hour" else "hours"
      in
        show days <> " " <> dayLabel <> " " <> show hours <> " " <> hourLabel
  | seconds >= 3600 =
      let
        hours = seconds / 3600
        minutes = (seconds `mod` 3600) / 60
        hourLabel = if hours == 1 then "hour" else "hours"
        minuteLabel = if minutes == 1 then "minute" else "minutes"
      in
        show hours <> " " <> hourLabel <> " " <> show minutes <> " " <> minuteLabel
  | seconds >= 60 =
      let
        minutes = seconds / 60
        minuteLabel = if minutes == 1 then "minute" else "minutes"
      in
        show minutes <> " " <> minuteLabel
  | otherwise = "a few seconds"

-- | Analyze rolling (5-hour) usage
-- | Rolling usage tracks usage over a 5-hour sliding window
analyzeRollingUsage :: { plan :: Int, usage :: Int, timeUpdated :: String } -> UsageAnalysis
analyzeRollingUsage { plan, usage, timeUpdated: _ } =
  let
    -- Usage limits based on plan
    limit = planToRollingLimit plan
    usagePercent = if limit == 0 then 0 else min 100 ((usage * 100) / limit)
    -- Reset time is calculated from 5-hour window
    resetInSec = 5 * 3600  -- simplified, would calculate based on timeUpdated
  in
    { usagePercent, resetInSec }

-- | Analyze weekly usage
analyzeWeeklyUsage :: { plan :: Int, usage :: Int, timeUpdated :: String } -> UsageAnalysis
analyzeWeeklyUsage { plan, usage, timeUpdated: _ } =
  let
    -- Usage limits based on plan
    limit = planToWeeklyLimit plan
    usagePercent = if limit == 0 then 0 else min 100 ((usage * 100) / limit)
    -- Reset time is calculated from weekly window
    resetInSec = 7 * 24 * 3600  -- simplified
  in
    { usagePercent, resetInSec }

-- | Get rolling usage limit based on plan
planToRollingLimit :: Int -> Int
planToRollingLimit plan = case plan of
  100 -> 500000   -- $100/month plan
  200 -> 1000000  -- $200/month plan
  _ -> 250000     -- default

-- | Get weekly usage limit based on plan
planToWeeklyLimit :: Int -> Int
planToWeeklyLimit plan = case plan of
  100 -> 2500000  -- $100/month plan
  200 -> 5000000  -- $200/month plan
  _ -> 1250000    -- default

-- | Usage display for UI
type UsageDisplay =
  { label :: String
  , usagePercent :: Int
  , resetTime :: String
  }

-- | Build usage display
buildUsageDisplay :: String -> UsageAnalysis -> UsageDisplay
buildUsageDisplay label analysis =
  { label
  , usagePercent: analysis.usagePercent
  , resetTime: "Resets in " <> formatResetTime analysis.resetInSec
  }

-- | Build rolling usage display
buildRollingUsageDisplay :: UsageAnalysis -> UsageDisplay
buildRollingUsageDisplay = buildUsageDisplay "5-hour Usage"

-- | Build weekly usage display
buildWeeklyUsageDisplay :: UsageAnalysis -> UsageDisplay
buildWeeklyUsageDisplay = buildUsageDisplay "Weekly Usage"

-- | Use balance form data
type UsageFormData =
  { workspaceId :: String
  , useBalance :: Boolean
  }

-- | Build use balance form data (toggle)
buildUseBalanceFormData :: String -> Boolean -> UsageFormData
buildUseBalanceFormData workspaceId currentValue =
  { workspaceId
  , useBalance: not currentValue  -- Toggle the value
  }

-- | Section content for subscription
type SubscriptionSectionContent =
  { title :: String
  , planDescription :: Int -> String
  }

-- | Default subscription section content
subscriptionSectionContent :: SubscriptionSectionContent
subscriptionSectionContent =
  { title: "Subscription"
  , planDescription: \plan -> "You are subscribed to OpenCode Black for $" <> show plan <> " per month."
  }

-- | Section content for waitlist
type WaitlistSectionContent =
  { title :: String
  , waitingDescription :: Int -> String
  , selectedDescription :: Int -> String
  , enrollNote :: String
  }

-- | Default waitlist section content
waitlistSectionContent :: WaitlistSectionContent
waitlistSectionContent =
  { title: "Waitlist"
  , waitingDescription: \plan -> "You are on the waitlist for the $" <> show plan <> " per month OpenCode Black plan."
  , selectedDescription: \plan -> "We're ready to enroll you into the $" <> show plan <> " per month OpenCode Black plan."
  , enrollNote: "When you click Enroll, your subscription starts immediately and your card will be charged."
  }

-- | Button state
type ButtonState =
  { disabled :: Boolean
  , label :: String
  }

-- | Manage subscription button state
manageButtonState :: { pending :: Boolean, redirecting :: Boolean } -> ButtonState
manageButtonState { pending, redirecting } =
  { disabled: pending || redirecting
  , label: if pending || redirecting then "Loading..." else "Manage Subscription"
  }

-- | Cancel waitlist button state
cancelButtonState :: { pending :: Boolean, cancelled :: Boolean } -> ButtonState
cancelButtonState { pending, cancelled } =
  { disabled: pending || cancelled
  , label: if pending then "Leaving..." else if cancelled then "Left" else "Leave Waitlist"
  }

-- | Enroll button state
enrollButtonState :: { pending :: Boolean, enrolled :: Boolean } -> ButtonState
enrollButtonState { pending, enrolled } =
  { disabled: pending || enrolled
  , label: if pending then "Enrolling..." else if enrolled then "Enrolled" else "Enroll"
  }

-- | Progress bar style
type ProgressBarStyle =
  { width :: String
  }

-- | Build progress bar style
buildProgressBarStyle :: Int -> ProgressBarStyle
buildProgressBarStyle percent =
  { width: show percent <> "%" }

-- | Use balance toggle label
useBalanceLabel :: String
useBalanceLabel = "Use your available balance after reaching the usage limits"
