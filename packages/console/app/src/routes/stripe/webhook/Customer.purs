-- | Stripe Webhook Customer Handlers
-- | Handles customer.updated events
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/stripe/webhook.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Stripe.Webhook.Customer
  ( handleCustomerUpdated
  , shouldProcessCustomerUpdated
  ) where

import Prelude

import Effect.Aff (Aff)
import Data.Maybe (Maybe(..), isJust)
import Console.App.Routes.Stripe.Webhook.Types (CustomerUpdatedData, PaymentMethodInfo)

-- | Check if customer.updated event should be processed
-- | Only processes if default payment method changed
shouldProcessCustomerUpdated :: CustomerUpdatedData -> Boolean
shouldProcessCustomerUpdated data =
  isJust data.previousAttributes &&
  isJust (data.previousAttributes >>= _.invoiceSettings) &&
  isJust ((data.previousAttributes >>= _.invoiceSettings) >>= _.defaultPaymentMethod)

-- | Handle customer.updated event
-- | Updates payment method in database (FFI boundary)
handleCustomerUpdated ::
  String ->  -- customerID
  String ->  -- paymentMethodID
  Aff Unit
handleCustomerUpdated customerID paymentMethodID = do
  -- Retrieve payment method from Stripe (FFI)
  paymentMethod <- retrievePaymentMethod paymentMethodID
  
  -- Update billing table (FFI - database operation)
  updateBillingPaymentMethod customerID paymentMethod

-- | Retrieve payment method from Stripe (FFI boundary)
foreign import retrievePaymentMethod :: String -> Aff PaymentMethodInfo

-- | Update billing table with payment method (FFI boundary - database)
foreign import updateBillingPaymentMethod :: String -> PaymentMethodInfo -> Aff Unit
