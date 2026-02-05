-- | Stripe Webhook Subscription Handlers
-- | Handles subscription events (created, updated, deleted)
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/stripe/webhook.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Stripe.Webhook.Subscription
  ( handleSubscriptionUpdated
  , handleSubscriptionDeleted
  , isIncompleteExpired
  ) where

import Prelude

import Effect.Aff (Aff)
import Console.App.Routes.Stripe.Webhook.Types (SubscriptionData)

-- | Check if subscription status is incomplete_expired
isIncompleteExpired :: SubscriptionData -> Boolean
isIncompleteExpired data =
  case data.status of
    Just "incomplete_expired" -> true
    _ -> false

-- | Handle subscription updated event
-- | Unsubscribes if status is incomplete_expired
handleSubscriptionUpdated :: SubscriptionData -> Aff Unit
handleSubscriptionUpdated data =
  if isIncompleteExpired data
    then unsubscribe data.subscriptionID
    else pure unit

-- | Handle subscription deleted event
handleSubscriptionDeleted :: SubscriptionData -> Aff Unit
handleSubscriptionDeleted data = unsubscribe data.subscriptionID

-- | Unsubscribe (FFI boundary - calls Billing.unsubscribe)
foreign import unsubscribe :: String -> Aff Unit
