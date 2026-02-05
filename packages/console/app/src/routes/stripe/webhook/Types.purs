-- | Stripe Webhook Types
-- | Pure PureScript types for Stripe webhook events
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/stripe/webhook.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Stripe.Webhook.Types
  ( StripeEventType(..)
  , StripeEvent(..)
  , CustomerUpdatedData
  , CheckoutSessionData
  , SubscriptionData
  , InvoiceData
  , ChargeData
  , PaymentMethodInfo
  , SubscriptionEnrichment
  ) where

import Prelude

import Data.Maybe (Maybe)

-- | Stripe webhook event types
data StripeEventType
  = CustomerUpdated
  | CheckoutSessionCompleted
  | CustomerSubscriptionCreated
  | CustomerSubscriptionUpdated
  | CustomerSubscriptionDeleted
  | InvoicePaymentSucceeded
  | InvoicePaymentFailed
  | InvoicePaymentActionRequired
  | ChargeRefunded
  | UnknownEvent String

-- | Stripe webhook event (pure PureScript type)
type StripeEvent =
  { type :: StripeEventType
  , data :: StripeEventData
  , created :: Int
  }

-- | Event data union (type-specific)
data StripeEventData
  = CustomerUpdatedData CustomerUpdatedData
  | CheckoutSessionData CheckoutSessionData
  | SubscriptionData SubscriptionData
  | InvoiceData InvoiceData
  | ChargeData ChargeData

-- | Customer updated event data
type CustomerUpdatedData =
  { customerID :: String
  , paymentMethodID :: Maybe String
  , previousAttributes :: Maybe { invoiceSettings :: Maybe { defaultPaymentMethod :: Maybe String } }
  }

-- | Checkout session completed event data
type CheckoutSessionData =
  { mode :: String  -- "payment" | "subscription"
  , workspaceID :: Maybe String
  , amountInCents :: Maybe Int
  , customerID :: Maybe String
  , customerEmail :: Maybe String
  , paymentID :: Maybe String
  , invoiceID :: Maybe String
  , subscriptionID :: Maybe String
  , promoCode :: Maybe String
  , customFields :: Array { key :: String, text :: Maybe { value :: String } }
  }

-- | Subscription event data
type SubscriptionData =
  { subscriptionID :: String
  , status :: Maybe String
  }

-- | Invoice event data
type InvoiceData =
  { invoiceID :: String
  , customerID :: Maybe String
  , workspaceID :: Maybe String
  , amountInCents :: Maybe Int
  , amountPaid :: Maybe Int
  , billingReason :: Maybe String  -- "subscription_create" | "subscription_cycle" | "manual"
  , subscriptionID :: Maybe String
  , metadata :: Maybe { workspaceID :: Maybe String, amount :: Maybe String }
  }

-- | Charge event data
type ChargeData =
  { customerID :: String
  , paymentIntentID :: String
  , created :: Int
  }

-- | Payment method information
type PaymentMethodInfo =
  { id :: String
  , last4 :: Maybe String
  , type :: String
  }

-- | Subscription payment enrichment
type SubscriptionEnrichment =
  { type :: String  -- "subscription"
  , couponID :: Maybe String
  }
