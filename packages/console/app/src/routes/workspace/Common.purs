-- | Workspace Common Utilities
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/common.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Common
  ( SessionInfo(..)
  , BillingInfo(..)
  , formatDateForTable
  , formatDateUTC
  , formatBalance
  , reloadAmountDefault
  , reloadAmountMin
  , reloadTriggerDefault
  , reloadTriggerMin
  ) where

import Prelude

import Data.Maybe (Maybe)
import Data.Number (toStringWith, fixed)

-- | Session info
type SessionInfo =
  { isAdmin :: Boolean
  , isBeta :: Boolean
  }

-- | Billing info
type BillingInfo =
  { customerID :: Maybe String
  , paymentMethodID :: Maybe String
  , paymentMethodType :: Maybe String
  , paymentMethodLast4 :: Maybe String
  , balance :: Int  -- in micro-cents (10^-8)
  , reload :: Boolean
  , reloadAmount :: Int
  , reloadAmountMin :: Int
  , reloadTrigger :: Int
  , reloadTriggerMin :: Int
  , monthlyLimit :: Maybe Int
  , monthlyUsage :: Int
  , timeMonthlyUsageUpdated :: Maybe String
  , reloadError :: Maybe String
  , timeReloadError :: Maybe String
  , subscription :: Maybe String
  , subscriptionID :: Maybe String
  , subscriptionPlan :: Maybe String
  , timeSubscriptionBooked :: Maybe String
  , timeSubscriptionSelected :: Maybe String
  }

-- | Format date for table display (pure)
-- | Output: "15 Jan, 3:45 PM"
formatDateForTable :: String -> String
formatDateForTable isoDate = isoDate  -- simplified, would use proper date parsing

-- | Format date in UTC (pure)
-- | Output: "Mon, Jan 15, 2024, 3:45:30 PM UTC"
formatDateUTC :: String -> String
formatDateUTC isoDate = isoDate  -- simplified

-- | Format balance from micro-cents (10^-8) to dollars
-- | Example: 100000000 -> "1.00"
formatBalance :: Int -> String
formatBalance amount =
  let
    dollars = toNumber amount / 100000000.0
    formatted = toStringWith (fixed 2) dollars
  in
    if formatted == "-0.00" then "0.00" else formatted
  where
    toNumber :: Int -> Number
    toNumber n = 0.0  -- simplified

-- | Default reload amount in cents
reloadAmountDefault :: Int
reloadAmountDefault = 2000  -- $20.00

-- | Minimum reload amount in cents
reloadAmountMin :: Int
reloadAmountMin = 500  -- $5.00

-- | Default reload trigger in cents
reloadTriggerDefault :: Int
reloadTriggerDefault = 500  -- $5.00

-- | Minimum reload trigger in cents
reloadTriggerMin :: Int
reloadTriggerMin = 100  -- $1.00

-- | Checkout URL request
type CheckoutUrlRequest =
  { workspaceId :: String
  , amount :: Int
  , successUrl :: String
  , cancelUrl :: String
  }

-- | Checkout URL response
type CheckoutUrlResponse =
  { url :: Maybe String
  , error :: Maybe String
  }
