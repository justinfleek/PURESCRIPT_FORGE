-- | Stripe Webhook Invoice Handlers
-- | Handles invoice.payment_succeeded, invoice.payment_failed, invoice.payment_action_required
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/stripe/webhook.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Stripe.Webhook.Invoice
  ( handleInvoicePaymentSucceeded
  , handleInvoicePaymentFailed
  , isSubscriptionBillingReason
  , isManualBillingReason
  , validateInvoicePayment
  ) where

import Prelude

import Effect.Aff (Aff)
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Console.App.Routes.Stripe.Webhook.Types (InvoiceData, SubscriptionEnrichment)
import Console.Core.Identifier (WorkspaceId)
import Console.Core.Util.Price (MicroCents)

-- | Validation error
type ValidationError = String

-- | Check if billing reason is subscription-related
isSubscriptionBillingReason :: InvoiceData -> Boolean
isSubscriptionBillingReason data =
  case data.billingReason of
    Just "subscription_create" -> true
    Just "subscription_cycle" -> true
    _ -> false

-- | Check if billing reason is manual
isManualBillingReason :: InvoiceData -> Boolean
isManualBillingReason data =
  case data.billingReason of
    Just "manual" -> true
    _ -> false

-- | Validate invoice payment data
validateInvoicePayment :: InvoiceData -> Either ValidationError Unit
validateInvoicePayment data =
  case data.customerID, data.invoiceID of
    Just _, Just _ -> Right unit
    Nothing, _ -> Left "Customer ID not found"
    _, Nothing -> Left "Invoice ID not found"

-- | Handle invoice payment succeeded (subscription)
handleInvoicePaymentSucceededSubscription ::
  String ->  -- invoiceID
  Int ->  -- amountPaid
  String ->  -- customerID
  String ->  -- subscriptionID
  Aff Unit
handleInvoicePaymentSucceededSubscription invoiceID amountPaid customerID subscriptionID = do
  -- Get coupon ID from subscription (FFI - Stripe API)
  couponID <- getCouponIDFromSubscription subscriptionID
  
  -- Get payment ID from invoice (FFI - Stripe API)
  paymentID <- getPaymentIDFromInvoice invoiceID
  
  -- Get workspace ID from customer (FFI - database)
  workspaceID <- getWorkspaceIDFromCustomer customerID
  
  -- Create payment record (FFI - database)
  createSubscriptionPayment workspaceID amountPaid paymentID invoiceID customerID couponID

-- | Handle invoice payment succeeded (manual)
handleInvoicePaymentSucceededManual ::
  WorkspaceId ->
  Int ->  -- amountInCents
  String ->  -- invoiceID
  String ->  -- customerID
  Aff Unit
handleInvoicePaymentSucceededManual workspaceID amountInCents invoiceID customerID = do
  -- Get payment ID from invoice (FFI - Stripe API)
  paymentID <- getPaymentIDFromInvoice invoiceID
  
  -- Update billing balance and create payment (FFI - database transaction)
  updateBillingBalanceAndCreatePayment workspaceID amountInCents invoiceID paymentID customerID

-- | Handle invoice payment failed/action required (manual)
handleInvoicePaymentFailed ::
  WorkspaceId ->
  String ->  -- invoiceID
  Aff Unit
handleInvoicePaymentFailed workspaceID invoiceID = do
  -- Get payment intent error message (FFI - Stripe API)
  errorMessage <- getPaymentIntentErrorMessage invoiceID
  
  -- Update billing with error (FFI - database)
  updateBillingPaymentError workspaceID errorMessage

-- | Route invoice payment succeeded handler
handleInvoicePaymentSucceeded :: InvoiceData -> Aff Unit
handleInvoicePaymentSucceeded data
  | isSubscriptionBillingReason data =
      case data.customerID, data.invoiceID, data.subscriptionID, data.amountPaid of
        Just customerID, Just invoiceID, Just subscriptionID, Just amountPaid ->
          handleInvoicePaymentSucceededSubscription invoiceID amountPaid customerID subscriptionID
        _, _, _, _ -> pure unit
  | isManualBillingReason data =
      case data.workspaceID, data.amountInCents, data.invoiceID, data.customerID of
        Just workspaceID, Just amountInCents, Just invoiceID, Just customerID ->
          handleInvoicePaymentSucceededManual workspaceID amountInCents invoiceID customerID
        _, _, _, _ -> pure unit
  | otherwise = pure unit

-- | FFI boundaries
foreign import getCouponIDFromSubscription :: String -> Aff (Maybe String)
foreign import getPaymentIDFromInvoice :: String -> Aff (Maybe String)
foreign import getWorkspaceIDFromCustomer :: String -> Aff WorkspaceId
foreign import createSubscriptionPayment :: WorkspaceId -> Int -> Maybe String -> String -> String -> Maybe String -> Aff Unit
foreign import updateBillingBalanceAndCreatePayment :: WorkspaceId -> Int -> String -> Maybe String -> String -> Aff Unit
foreign import getPaymentIntentErrorMessage :: String -> Aff (Maybe String)
foreign import updateBillingPaymentError :: WorkspaceId -> Maybe String -> Aff Unit
