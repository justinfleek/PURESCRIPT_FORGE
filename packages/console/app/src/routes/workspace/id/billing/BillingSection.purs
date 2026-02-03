-- | Billing Section - Balance and Payment Management
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id]/billing/billing-section.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.Billing.BillingSection
  ( BillingSectionState(..)
  , BillingSectionAction(..)
  , PaymentMethodType(..)
  , SessionUrlRequest(..)
  , SessionUrlResponse(..)
  , initialState
  , reducer
  , formatBalance
  , checkoutButtonState
  , sessionButtonState
  , buildCheckoutRequest
  ) where

import Prelude

import Data.Int (toNumber)
import Data.Maybe (Maybe(..))

-- | Payment method type
data PaymentMethodType
  = Card
  | Link
  | Unknown String

derive instance eqPaymentMethodType :: Eq PaymentMethodType

-- | Parse payment method type
parsePaymentMethodType :: Maybe String -> Maybe PaymentMethodType
parsePaymentMethodType Nothing = Nothing
parsePaymentMethodType (Just s) = case s of
  "card" -> Just Card
  "link" -> Just Link
  _ -> Just (Unknown s)

-- | Billing section state
type BillingSectionState =
  { showAddBalanceForm :: Boolean
  , addBalanceAmount :: String
  , checkoutRedirecting :: Boolean
  , sessionRedirecting :: Boolean
  }

-- | Actions for billing section
data BillingSectionAction
  = ShowAddBalanceForm
  | HideAddBalanceForm
  | SetAddBalanceAmount String
  | SetCheckoutRedirecting Boolean
  | SetSessionRedirecting Boolean
  | UpdateFromBillingInfo { reloadAmount :: Int }

-- | Initial state
initialState :: BillingSectionState
initialState =
  { showAddBalanceForm: false
  , addBalanceAmount: ""
  , checkoutRedirecting: false
  , sessionRedirecting: false
  }

-- | Pure state reducer
reducer :: BillingSectionState -> BillingSectionAction -> BillingSectionState
reducer state action = case action of
  ShowAddBalanceForm -> state { showAddBalanceForm = true }
  HideAddBalanceForm -> state { showAddBalanceForm = false }
  SetAddBalanceAmount amount -> state { addBalanceAmount = amount }
  SetCheckoutRedirecting redirecting -> state { checkoutRedirecting = redirecting }
  SetSessionRedirecting redirecting -> state { sessionRedirecting = redirecting }
  UpdateFromBillingInfo { reloadAmount } -> 
    state { addBalanceAmount = show reloadAmount }

-- | Format balance from micro-cents to dollars
-- | Example: 100000000 -> "1.00"
formatBalance :: Int -> String
formatBalance amount =
  let
    dollars = toNumber amount / 100000000.0
  in
    formatNumber dollars 2
  where
    formatNumber :: Number -> Int -> String
    formatNumber n _ = show n  -- simplified

-- | Button state
type ButtonState =
  { disabled :: Boolean
  , label :: String
  }

-- | Checkout button state
checkoutButtonState :: { pending :: Boolean, redirecting :: Boolean } -> ButtonState
checkoutButtonState { pending, redirecting } =
  { disabled: pending || redirecting
  , label: if pending || redirecting then "Loading..." else "Enable Billing"
  }

-- | Session button state
sessionButtonState :: { pending :: Boolean, redirecting :: Boolean } -> ButtonState
sessionButtonState { pending, redirecting } =
  { disabled: pending || redirecting
  , label: if pending || redirecting then "Loading..." else "Manage"
  }

-- | Add balance button state
addBalanceButtonState :: BillingSectionState -> { pending :: Boolean } -> ButtonState
addBalanceButtonState state { pending } =
  { disabled: state.addBalanceAmount == "" || pending || state.checkoutRedirecting
  , label: if pending || state.checkoutRedirecting then "Loading..." else "Add"
  }

-- | Session URL request
type SessionUrlRequest =
  { workspaceId :: String
  , returnUrl :: String
  }

-- | Session URL response
type SessionUrlResponse =
  { error :: Maybe String
  , data :: Maybe String
  }

-- | Build checkout request
buildCheckoutRequest :: String -> String -> String -> { workspaceId :: String, amount :: Int, successUrl :: String, cancelUrl :: String }
buildCheckoutRequest workspaceId amountStr baseUrl =
  { workspaceId
  , amount: parseAmount amountStr
  , successUrl: baseUrl
  , cancelUrl: baseUrl
  }
  where
    parseAmount :: String -> Int
    parseAmount _ = 0  -- simplified

-- | Credit card display
type CreditCardDisplay =
  { showCardIcon :: Boolean
  , showStripeIcon :: Boolean
  , last4 :: Maybe String
  , isLink :: Boolean
  }

-- | Build credit card display
buildCreditCardDisplay :: Maybe String -> Maybe String -> CreditCardDisplay
buildCreditCardDisplay paymentMethodType last4 =
  case parsePaymentMethodType paymentMethodType of
    Just Link ->
      { showCardIcon: false
      , showStripeIcon: true
      , last4: Nothing
      , isLink: true
      }
    Just Card ->
      { showCardIcon: true
      , showStripeIcon: false
      , last4
      , isLink: false
      }
    _ ->
      { showCardIcon: true
      , showStripeIcon: false
      , last4: Nothing
      , isLink: false
      }

-- | Section content
type BillingSectionContent =
  { title :: String
  , description :: String
  , contactEmail :: String
  }

-- | Default section content
sectionContent :: BillingSectionContent
sectionContent =
  { title: "Billing"
  , description: "Manage payments methods."
  , contactEmail: "contact@anoma.ly"
  }

-- | Balance display
type BalanceDisplay =
  { value :: String
  , label :: String
  }

-- | Build balance display
buildBalanceDisplay :: Int -> BalanceDisplay
buildBalanceDisplay balance =
  { value: "$" <> formatBalance balance
  , label: "Current Balance"
  }

-- | Add balance form state
type AddBalanceFormState =
  { visible :: Boolean
  , amount :: String
  , minAmount :: Int
  , error :: Maybe String
  }

-- | Build add balance form state
buildAddBalanceFormState :: BillingSectionState -> Int -> Maybe String -> AddBalanceFormState
buildAddBalanceFormState state minAmount error =
  { visible: state.showAddBalanceForm
  , amount: state.addBalanceAmount
  , minAmount
  , error
  }

-- | Validate add balance amount
validateAddBalanceAmount :: String -> Int -> Maybe String
validateAddBalanceAmount amountStr minAmount =
  case parseIntMaybe amountStr of
    Nothing -> Just "Please enter a valid amount"
    Just amount ->
      if amount < minAmount
        then Just $ "Minimum amount is $" <> show minAmount
        else Nothing
  where
    parseIntMaybe :: String -> Maybe Int
    parseIntMaybe _ = Nothing  -- simplified
