-- | Stripe Webhook Main Handler
-- | Orchestrates Stripe webhook event routing
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/stripe/webhook.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Stripe.Webhook.Main
  ( handleWebhookPOST
  ) where

import Prelude

import Effect.Aff (Aff)
import Data.Maybe (Maybe(..))
import Console.App.FFI.SolidStart (APIEvent, Response)
import Console.App.Routes.Stripe.Webhook.Types (StripeEventType(..), CustomerUpdatedData, CheckoutSessionData, SubscriptionData, InvoiceData, ChargeData)
import Console.App.Routes.Stripe.Webhook.Customer (handleCustomerUpdated, shouldProcessCustomerUpdated)
import Console.App.Routes.Stripe.Webhook.Checkout (handleCheckoutPayment, handleCheckoutSubscription, validateCheckoutPayment, validateCheckoutSubscription, extractWorkspaceID)
import Console.App.Routes.Stripe.Webhook.Subscription (handleSubscriptionUpdated, handleSubscriptionDeleted, isIncompleteExpired)
import Console.App.Routes.Stripe.Webhook.Invoice (handleInvoicePaymentSucceeded, handleInvoicePaymentFailed, isManualBillingReason)
import Console.App.Routes.Stripe.Webhook.Charge (handleChargeRefunded, validateChargeRefunded)

-- | Handle Stripe webhook POST request
handleWebhookPOST :: APIEvent -> Aff Response
handleWebhookPOST event = do
  -- Construct Stripe event (FFI boundary)
  { type: eventType, data: eventDataJson, created } <- constructStripeEvent event
  
  -- Log event (FFI - system logging)
  logStripeEvent eventType eventDataJson
  
  -- Parse event type
  let parsedType = parseEventType eventType
  
  -- Route to appropriate handler
  result <- routeEvent parsedType eventDataJson created
  
  -- Return response
  createSuccessResponse result

-- | Parse event type string to StripeEventType
parseEventType :: String -> StripeEventType
parseEventType "customer.updated" = CustomerUpdated
parseEventType "checkout.session.completed" = CheckoutSessionCompleted
parseEventType "customer.subscription.created" = CustomerSubscriptionCreated
parseEventType "customer.subscription.updated" = CustomerSubscriptionUpdated
parseEventType "customer.subscription.deleted" = CustomerSubscriptionDeleted
parseEventType "invoice.payment_succeeded" = InvoicePaymentSucceeded
parseEventType "invoice.payment_failed" = InvoicePaymentFailed
parseEventType "invoice.payment_action_required" = InvoicePaymentActionRequired
parseEventType "charge.refunded" = ChargeRefunded
parseEventType unknown = UnknownEvent unknown

-- | Route event to appropriate handler
routeEvent :: StripeEventType -> String -> Int -> Aff (Maybe String)
routeEvent eventType eventDataJson created = case eventType of
  CustomerUpdated -> do
    data <- parseCustomerUpdatedData eventDataJson
    if shouldProcessCustomerUpdated data
      then do
        case data.paymentMethodID of
          Just paymentMethodID -> do
            handleCustomerUpdated data.customerID paymentMethodID
            pure (Just "done")
          Nothing -> pure (Just "ignored")
      else pure (Just "ignored")
  
  CheckoutSessionCompleted -> do
    data <- parseCheckoutSessionData eventDataJson
    case data.mode of
      "payment" ->
        case validateCheckoutPayment data of
          Left _ -> pure Nothing
          Right _ ->
            case extractWorkspaceID data, data.amountInCents, data.customerID, data.paymentID, data.invoiceID of
              Just workspaceID, Just amount, Just customerID, Just paymentID, Just invoiceID -> do
                handleCheckoutPayment workspaceID amount customerID paymentID invoiceID
                pure (Just "done")
              _, _, _, _, _ -> pure Nothing
      
      "subscription" ->
        case validateCheckoutSubscription data of
          Left _ -> pure Nothing
          Right _ ->
            case extractWorkspaceID data, data.amountInCents, data.customerID, data.customerEmail, data.invoiceID, data.subscriptionID of
              Just workspaceID, Just amount, Just customerID, Just email, Just invoiceID, Just subscriptionID -> do
                handleCheckoutSubscription workspaceID amount customerID email invoiceID subscriptionID data.promoCode
                pure (Just "done")
              _, _, _, _, _, _ -> pure Nothing
      
      _ -> pure (Just "ignored")
  
  CustomerSubscriptionUpdated -> do
    data <- parseSubscriptionData eventDataJson
    if isIncompleteExpired data
      then do
        handleSubscriptionUpdated data
        pure (Just "done")
      else pure (Just "ignored")
  
  CustomerSubscriptionDeleted -> do
    data <- parseSubscriptionData eventDataJson
    handleSubscriptionDeleted data
    pure (Just "done")
  
  InvoicePaymentSucceeded -> do
    data <- parseInvoiceData eventDataJson
    handleInvoicePaymentSucceeded data
    pure (Just "done")
  
  InvoicePaymentFailed -> do
    data <- parseInvoiceData eventDataJson
    if isManualBillingReason data
      then
        case data.workspaceID, data.invoiceID of
          Just workspaceID, Just invoiceID -> do
            handleInvoicePaymentFailed workspaceID invoiceID
            pure (Just "done")
          _, _ -> pure Nothing
      else pure (Just "ignored")
  
  InvoicePaymentActionRequired -> do
    data <- parseInvoiceData eventDataJson
    if isManualBillingReason data
      then
        case data.workspaceID, data.invoiceID of
          Just workspaceID, Just invoiceID -> do
            handleInvoicePaymentFailed workspaceID invoiceID
            pure (Just "done")
          _, _ -> pure Nothing
      else pure (Just "ignored")
  
  ChargeRefunded -> do
    data <- parseChargeData eventDataJson created
    case validateChargeRefunded data of
      Left _ -> pure Nothing
      Right _ -> do
        handleChargeRefunded data
        pure (Just "done")
  
  CustomerSubscriptionCreated -> pure (Just "ignored")  -- No-op (commented out in original)
  
  UnknownEvent _ -> pure (Just "ignored")

-- | Parse event data from JSON (FFI boundary)
foreign import parseCustomerUpdatedData :: String -> Aff CustomerUpdatedData
foreign import parseCheckoutSessionData :: String -> Aff CheckoutSessionData
foreign import parseSubscriptionData :: String -> Aff SubscriptionData
foreign import parseInvoiceData :: String -> Aff InvoiceData
foreign import parseChargeData :: String -> Int -> Aff ChargeData

-- | Construct Stripe event from API event (FFI boundary)
-- | Returns event type and JSON data string
foreign import constructStripeEvent :: APIEvent -> Aff { type :: String, data :: String, created :: Int }

-- | Log Stripe event (FFI - system logging)
foreign import logStripeEvent :: String -> String -> Aff Unit

-- | Create success response (FFI boundary)
foreign import createSuccessResponse :: Maybe String -> Aff Response

-- | Create error response (FFI boundary)
foreign import createErrorResponse :: String -> Aff Response
