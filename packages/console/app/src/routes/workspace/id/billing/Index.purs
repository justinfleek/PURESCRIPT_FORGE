-- | Billing Index Page
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id]/billing/index.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.Billing.Index
  ( BillingPageSections(..)
  , determineSections
  ) where

import Prelude

import Data.Maybe (Maybe(..), isJust)
import Console.App.Routes.Workspace.Common (BillingInfo)

-- | Which sections to display on billing page
type BillingPageSections =
  { showBlackSection :: Boolean
  , showBillingSection :: Boolean
  , showReloadSection :: Boolean
  , showMonthlyLimitSection :: Boolean
  , showPaymentSection :: Boolean
  }

-- | Determine which sections to display based on billing info
determineSections :: { isAdmin :: Boolean } -> Maybe BillingInfo -> BillingPageSections
determineSections userInfo mbBillingInfo =
  case mbBillingInfo of
    Nothing ->
      { showBlackSection: false
      , showBillingSection: false
      , showReloadSection: false
      , showMonthlyLimitSection: false
      , showPaymentSection: false
      }
    Just billingInfo ->
      if userInfo.isAdmin
        then
          { showBlackSection: hasSubscription billingInfo
          , showBillingSection: true
          , showReloadSection: hasCustomer billingInfo
          , showMonthlyLimitSection: hasCustomer billingInfo
          , showPaymentSection: hasCustomer billingInfo
          }
        else
          { showBlackSection: false
          , showBillingSection: false
          , showReloadSection: false
          , showMonthlyLimitSection: false
          , showPaymentSection: false
          }
  where
    hasSubscription :: BillingInfo -> Boolean
    hasSubscription info = isJust info.subscriptionID || isJust info.timeSubscriptionBooked
    
    hasCustomer :: BillingInfo -> Boolean
    hasCustomer info = isJust info.customerID

-- | Page content
type BillingPageContent =
  { page :: String
  , slot :: String
  }

-- | Default page content
billingPageContent :: BillingPageContent
billingPageContent =
  { page: "workspace-[id]"
  , slot: "sections"
  }
