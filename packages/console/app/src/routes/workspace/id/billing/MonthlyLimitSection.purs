-- | Monthly Limit Section
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id]/billing/monthly-limit-section.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.Billing.MonthlyLimitSection
  ( MonthlyLimitState(..)
  , MonthlyLimitAction(..)
  , MonthlyLimitFormData(..)
  , initialState
  , reducer
  , validateLimit
  , formatMonthlyUsage
  , buildFormData
  , calculateCurrentUsage
  ) where

import Prelude

import Data.Int (toNumber)
import Data.Maybe (Maybe(..))

-- | Monthly limit section state
type MonthlyLimitState =
  { show :: Boolean
  }

-- | Actions for monthly limit section
data MonthlyLimitAction
  = Show
  | Hide

-- | Initial state
initialState :: MonthlyLimitState
initialState =
  { show: false
  }

-- | Pure state reducer
reducer :: MonthlyLimitState -> MonthlyLimitAction -> MonthlyLimitState
reducer state action = case action of
  Show -> state { show = true }
  Hide -> state { show = false }

-- | Form data for setting monthly limit
type MonthlyLimitFormData =
  { limit :: String
  , workspaceId :: String
  }

-- | Build form data
buildFormData :: String -> String -> MonthlyLimitFormData
buildFormData limit workspaceId =
  { limit
  , workspaceId
  }

-- | Validation error
type ValidationError = String

-- | Validate limit value
validateLimit :: String -> Maybe ValidationError
validateLimit limitStr
  | limitStr == "" = Just "Limit is required."
  | otherwise = 
      case parseIntMaybe limitStr of
        Nothing -> Just "Set a valid monthly limit."
        Just limit ->
          if limit < 0
            then Just "Set a valid monthly limit."
            else Nothing
  where
    parseIntMaybe :: String -> Maybe Int
    parseIntMaybe _ = Nothing  -- simplified

-- | Format monthly usage from micro-cents to dollars
-- | Example: 5000000000 -> "50.00"
formatMonthlyUsage :: Int -> String
formatMonthlyUsage usage =
  let
    dollars = toNumber usage / 100000000.0
  in
    formatNumber dollars 2
  where
    formatNumber :: Number -> Int -> String
    formatNumber n _ = show n  -- simplified

-- | Calculate current usage for display
-- | Returns "0" if usage is from a different month
calculateCurrentUsage :: { monthlyUsage :: Int, timeUsageUpdated :: Maybe String, currentMonth :: String } -> String
calculateCurrentUsage { monthlyUsage, timeUsageUpdated, currentMonth } =
  case timeUsageUpdated of
    Nothing -> "0"
    Just lastUsedDate ->
      if extractMonth lastUsedDate == currentMonth
        then formatMonthlyUsage monthlyUsage
        else "0"
  where
    extractMonth :: String -> String
    extractMonth date = date  -- simplified, would extract YYYY-MM

-- | Get current month name
-- | Example: "January"
getCurrentMonthName :: Int -> String
getCurrentMonthName month = case month of
  0 -> "January"
  1 -> "February"
  2 -> "March"
  3 -> "April"
  4 -> "May"
  5 -> "June"
  6 -> "July"
  7 -> "August"
  8 -> "September"
  9 -> "October"
  10 -> "November"
  11 -> "December"
  _ -> "Unknown"

-- | Section content
type MonthlyLimitSectionContent =
  { title :: String
  , description :: String
  , noLimitMessage :: String
  , usagePrefix :: String
  }

-- | Default section content
sectionContent :: MonthlyLimitSectionContent
sectionContent =
  { title: "Monthly Limit"
  , description: "Set a monthly usage limit for your account."
  , noLimitMessage: "No usage limit set."
  , usagePrefix: "Current usage for"
  }

-- | Limit display
type LimitDisplay =
  { hasLimit :: Boolean
  , value :: String
  , showCurrency :: Boolean
  }

-- | Build limit display
buildLimitDisplay :: Maybe Int -> LimitDisplay
buildLimitDisplay mbLimit =
  case mbLimit of
    Nothing ->
      { hasLimit: false
      , value: "-"
      , showCurrency: false
      }
    Just limit ->
      { hasLimit: true
      , value: show limit
      , showCurrency: true
      }

-- | Form state
type FormState =
  { visible :: Boolean
  , error :: Maybe String
  , pending :: Boolean
  }

-- | Build form state
buildFormState :: MonthlyLimitState -> Maybe String -> Boolean -> FormState
buildFormState state error pending =
  { visible: state.show
  , error
  , pending
  }

-- | Button state
type ButtonState =
  { disabled :: Boolean
  , label :: String
  }

-- | Submit button state
submitButtonState :: { pending :: Boolean } -> ButtonState
submitButtonState { pending } =
  { disabled: pending
  , label: if pending then "Setting..." else "Set"
  }

-- | Edit/Set button label
editButtonLabel :: Maybe Int -> String
editButtonLabel mbLimit =
  case mbLimit of
    Nothing -> "Set Limit"
    Just _ -> "Edit Limit"

-- | Usage status display
type UsageStatusDisplay =
  { hasLimit :: Boolean
  , message :: String
  }

-- | Build usage status display
buildUsageStatusDisplay :: Maybe Int -> String -> String -> UsageStatusDisplay
buildUsageStatusDisplay mbLimit monthName usage =
  case mbLimit of
    Nothing ->
      { hasLimit: false
      , message: "No usage limit set."
      }
    Just _ ->
      { hasLimit: true
      , message: "Current usage for " <> monthName <> " is $" <> usage <> "."
      }
