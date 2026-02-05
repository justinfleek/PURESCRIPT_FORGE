-- | Stripe Webhook Charge Handlers
-- | Handles charge.refunded events
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/stripe/webhook.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Stripe.Webhook.Charge
  ( handleChargeRefunded
  , validateChargeRefunded
  ) where

import Prelude

import Effect.Aff (Aff)
import Data.Either (Either(..))
import Console.App.Routes.Stripe.Webhook.Types (ChargeData)
import Console.Core.Identifier (WorkspaceId)
import Console.Core.Util.Price (MicroCents)

-- | Validation error
type ValidationError = String

-- | Validate charge refunded data
validateChargeRefunded :: ChargeData -> Either ValidationError Unit
validateChargeRefunded data =
  if data.customerID == "" || data.paymentIntentID == ""
    then Left "Customer ID or Payment Intent ID not found"
    else Right unit

-- | Handle charge refunded event
handleChargeRefunded :: ChargeData -> Aff Unit
handleChargeRefunded data = do
  -- Get workspace ID from customer (FFI - database)
  workspaceID <- getWorkspaceIDFromCustomer data.customerID
  
  -- Get payment amount (FFI - database)
  amount <- getPaymentAmount workspaceID data.paymentIntentID
  
  -- Update payment and billing (FFI - database transaction)
  updatePaymentAndBillingForRefund workspaceID data.paymentIntentID data.created amount

-- | FFI boundaries
foreign import getWorkspaceIDFromCustomer :: String -> Aff WorkspaceId
foreign import getPaymentAmount :: WorkspaceId -> String -> Aff MicroCents
foreign import updatePaymentAndBillingForRefund :: WorkspaceId -> String -> Int -> MicroCents -> Aff Unit
