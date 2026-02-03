-- | Billing Schema
-- |
-- | Database schema for billing, payments, subscriptions, and usage.
-- | Handles Stripe integration and consumption tracking.
-- |
-- | Source: _OTHER/opencode-original/packages/console/core/src/schema/billing.sql.ts
module Forge.Console.Core.Schema.Billing
  ( Billing
  , BillingId
  , Payment
  , PaymentId
  , Subscription
  , SubscriptionId
  , Usage
  , UsageId
  , SubscriptionPlan(..)
  , SubscriptionStatus(..)
  , SubscriptionData
  , PaymentEnrichment(..)
  , allSubscriptionPlans
  ) where

import Prelude

import Data.DateTime (DateTime)
import Data.Maybe (Maybe)
import Forge.Console.Core.Schema.Types (ULID)
import Forge.Console.Core.Schema.Workspace (WorkspaceId)
import Forge.Console.Core.Schema.User (UserId)
import Forge.Console.Core.Schema.Key (KeyId)

-- | Billing ID type
type BillingId = ULID

-- | Payment ID type
type PaymentId = ULID

-- | Subscription ID type  
type SubscriptionId = ULID

-- | Usage ID type
type UsageId = ULID

-- | Subscription plans (monthly credit limits)
data SubscriptionPlan
  = Plan20   -- $20/month
  | Plan100  -- $100/month
  | Plan200  -- $200/month

derive instance eqSubscriptionPlan :: Eq SubscriptionPlan

instance showSubscriptionPlan :: Show SubscriptionPlan where
  show Plan20 = "20"
  show Plan100 = "100"
  show Plan200 = "200"

-- | All subscription plans
allSubscriptionPlans :: Array SubscriptionPlan
allSubscriptionPlans = [Plan20, Plan100, Plan200]

-- | Subscription status
data SubscriptionStatus
  = Subscribed

derive instance eqSubscriptionStatus :: Eq SubscriptionStatus

instance showSubscriptionStatus :: Show SubscriptionStatus where
  show Subscribed = "subscribed"

-- | Subscription data stored as JSON
type SubscriptionData =
  { status :: SubscriptionStatus
  , seats :: Int
  , plan :: SubscriptionPlan
  , useBalance :: Maybe Boolean
  , coupon :: Maybe String
  }

-- | Payment enrichment data
data PaymentEnrichment
  = SubscriptionPayment { couponID :: Maybe String }
  | CreditPayment

derive instance eqPaymentEnrichment :: Eq PaymentEnrichment

-- | Billing entity (one per workspace)
type Billing =
  { workspaceID :: WorkspaceId
  , id :: BillingId
  , customerID :: Maybe String           -- Stripe customer ID
  , paymentMethodID :: Maybe String      -- Stripe payment method
  , paymentMethodType :: Maybe String    -- card, etc.
  , paymentMethodLast4 :: Maybe String   -- Last 4 digits
  , balance :: Int                       -- Balance in micro-cents
  , monthlyLimit :: Maybe Int
  , monthlyUsage :: Maybe Int
  , timeMonthlyUsageUpdated :: Maybe DateTime
  , reload :: Maybe Boolean
  , reloadTrigger :: Maybe Int           -- Balance threshold to trigger reload
  , reloadAmount :: Maybe Int            -- Amount to reload
  , reloadError :: Maybe String
  , timeReloadError :: Maybe DateTime
  , timeReloadLockedTill :: Maybe DateTime
  , subscription :: Maybe SubscriptionData
  , subscriptionID :: Maybe String       -- Stripe subscription ID
  , subscriptionPlan :: Maybe SubscriptionPlan
  , timeSubscriptionBooked :: Maybe DateTime
  , timeSubscriptionSelected :: Maybe DateTime
  , timeCreated :: DateTime
  , timeUpdated :: DateTime
  , timeDeleted :: Maybe DateTime
  }

-- | Subscription entity (per user in workspace with subscription)
type Subscription =
  { workspaceID :: WorkspaceId
  , id :: SubscriptionId
  , userID :: UserId
  , rollingUsage :: Maybe Int
  , fixedUsage :: Maybe Int
  , timeRollingUpdated :: Maybe DateTime
  , timeFixedUpdated :: Maybe DateTime
  , timeCreated :: DateTime
  , timeUpdated :: DateTime
  , timeDeleted :: Maybe DateTime
  }

-- | Payment entity
type Payment =
  { workspaceID :: WorkspaceId
  , id :: PaymentId
  , customerID :: Maybe String
  , invoiceID :: Maybe String
  , paymentID :: Maybe String
  , amount :: Int                        -- Amount in micro-cents
  , timeRefunded :: Maybe DateTime
  , enrichment :: Maybe PaymentEnrichment
  , timeCreated :: DateTime
  , timeUpdated :: DateTime
  , timeDeleted :: Maybe DateTime
  }

-- | Usage entity (API consumption records)
type Usage =
  { workspaceID :: WorkspaceId
  , id :: UsageId
  , model :: String
  , provider :: String
  , inputTokens :: Int
  , outputTokens :: Int
  , reasoningTokens :: Maybe Int
  , cacheReadTokens :: Maybe Int
  , cacheWrite5mTokens :: Maybe Int
  , cacheWrite1hTokens :: Maybe Int
  , cost :: Int                          -- Cost in micro-cents
  , keyID :: Maybe KeyId
  , timeCreated :: DateTime
  , timeUpdated :: DateTime
  , timeDeleted :: Maybe DateTime
  }
