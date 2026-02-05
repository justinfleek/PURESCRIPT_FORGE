-- | Stripe Webhook Checkout Handlers
-- | Handles checkout.session.completed events (payment and subscription modes)
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/stripe/webhook.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Stripe.Webhook.Checkout
  ( handleCheckoutPayment
  , handleCheckoutSubscription
  , extractWorkspaceID
  , validateCheckoutPayment
  , validateCheckoutSubscription
  ) where

import Prelude

import Effect.Aff (Aff)
import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Array (find) as Array
import Console.App.Routes.Stripe.Webhook.Types (CheckoutSessionData, PaymentMethodInfo)
import Console.Core.Identifier (WorkspaceId, UserId)

-- | Validation error
type ValidationError = String

-- | Validate checkout payment data
validateCheckoutPayment :: CheckoutSessionData -> Either ValidationError Unit
validateCheckoutPayment data =
  case data.workspaceID, data.customerID, data.amountInCents, data.paymentID, data.invoiceID of
    Just _, Just _, Just _, Just _, Just _ -> Right unit
    Nothing, _, _, _, _ -> Left "Workspace ID not found"
    _, Nothing, _, _, _ -> Left "Customer ID not found"
    _, _, Nothing, _, _ -> Left "Amount not found"
    _, _, _, Nothing, _ -> Left "Payment ID not found"
    _, _, _, _, Nothing -> Left "Invoice ID not found"

-- | Validate checkout subscription data
validateCheckoutSubscription :: CheckoutSessionData -> Either ValidationError Unit
validateCheckoutSubscription data =
  case data.workspaceID, data.customerID, data.amountInCents, data.invoiceID, data.subscriptionID of
    Just _, Just _, Just _, Just _, Just _ -> Right unit
    Nothing, _, _, _, _ -> Left "Workspace ID not found"
    _, Nothing, _, _, _ -> Left "Customer ID not found"
    _, _, Nothing, _, _ -> Left "Amount not found"
    _, _, _, Nothing, _ -> Left "Invoice ID not found"
    _, _, _, _, Nothing -> Left "Subscription ID not found"

-- | Extract workspace ID from checkout session
extractWorkspaceID :: CheckoutSessionData -> Maybe WorkspaceId
extractWorkspaceID data =
  case data.mode of
    "payment" -> data.workspaceID
    "subscription" ->
      case findCustomField "workspaceid" data.customFields of
        Just value -> Just value
        Nothing -> Nothing
    _ -> Nothing

-- | Find custom field by key (pure PureScript)
findCustomField :: String -> Array { key :: String, text :: Maybe { value :: String } } -> Maybe String
findCustomField key fields =
  case Array.find (\f -> f.key == key) fields of
    Just field -> field.text >>= _.value
    Nothing -> Nothing

-- | Handle checkout payment completion
handleCheckoutPayment ::
  WorkspaceId ->
  Int ->  -- amountInCents
  String ->  -- customerID
  String ->  -- paymentID
  String ->  -- invoiceID
  Aff Unit
handleCheckoutPayment workspaceID amountInCents customerID paymentID invoiceID = do
  -- Verify customer ID matches (FFI - database)
  customerMatches <- verifyCustomerID workspaceID customerID
  
  -- Set customer metadata if new customer (FFI - Stripe API)
  when (not customerMatches) $
    updateCustomerMetadata customerID workspaceID
  
  -- Get payment method (FFI - Stripe API)
  paymentMethod <- retrievePaymentMethodFromIntent paymentID
  
  -- Update billing and create payment (FFI - database transaction)
  updateBillingAndCreatePayment
    workspaceID
    amountInCents
    customerID
    paymentID
    invoiceID
    paymentMethod
    (not customerMatches)  -- isFirstTime

-- | Handle checkout subscription completion
handleCheckoutSubscription ::
  WorkspaceId ->
  Int ->  -- amountInCents
  String ->  -- customerID
  String ->  -- customerEmail
  String ->  -- invoiceID
  String ->  -- subscriptionID
  Maybe String ->  -- promoCode
  Aff Unit
handleCheckoutSubscription workspaceID amountInCents customerID customerEmail invoiceID subscriptionID promoCode = do
  -- Get payment ID from invoice (FFI - Stripe API)
  paymentID <- getPaymentIDFromInvoice invoiceID
  
  -- Get payment method (FFI - Stripe API)
  paymentMethod <- retrievePaymentMethodFromIntent paymentID
  
  -- Get coupon ID if promo code exists (FFI - Stripe API)
  couponID <- case promoCode of
    Just code -> getCouponIDFromPromoCode code
    Nothing -> pure Nothing
  
  -- Find user by email (FFI - database)
  userID <- findUserByEmail workspaceID customerEmail
  
  -- Update billing and create subscription (FFI - database transaction)
  updateBillingAndCreateSubscription
    workspaceID
    customerID
    subscriptionID
    paymentMethod
    couponID
    userID
    amountInCents
    paymentID
    invoiceID

-- | Conditional execution
when :: Boolean -> Aff Unit -> Aff Unit
when true action = action
when false _ = pure unit

-- | FFI boundaries
foreign import verifyCustomerID :: WorkspaceId -> String -> Aff Boolean
foreign import updateCustomerMetadata :: String -> WorkspaceId -> Aff Unit
foreign import retrievePaymentMethodFromIntent :: String -> Aff PaymentMethodInfo
foreign import updateBillingAndCreatePayment :: WorkspaceId -> Int -> String -> String -> String -> PaymentMethodInfo -> Boolean -> Aff Unit
foreign import getPaymentIDFromInvoice :: String -> Aff String
foreign import getCouponIDFromPromoCode :: String -> Aff (Maybe String)
foreign import findUserByEmail :: WorkspaceId -> String -> Aff UserId
foreign import updateBillingAndCreateSubscription :: WorkspaceId -> String -> String -> PaymentMethodInfo -> Maybe String -> UserId -> Int -> String -> String -> Aff Unit
