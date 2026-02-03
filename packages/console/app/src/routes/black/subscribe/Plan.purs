-- | Black Subscribe Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/black/subscribe/[plan].tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Black.Subscribe.Plan
  ( SubscribeState(..)
  , SubscribeAction(..)
  , WorkspaceBilling(..)
  , WorkspaceWithBilling(..)
  , SuccessData(..)
  , SetupIntentResult(..)
  , BookingRequest(..)
  , SubscribeResult(..)
  , initialState
  , reducer
  , validatePlan
  , shouldShowWorkspacePicker
  , buildBookingRequest
  ) where

import Prelude

import Data.Array (length, head, find)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), isNothing)
import Console.App.Routes.Black.Common (PlanId(..), isValidPlanId)

-- | Workspace billing information
type WorkspaceBilling =
  { customerID :: Maybe String
  , paymentMethodID :: Maybe String
  , paymentMethodType :: Maybe String
  , paymentMethodLast4 :: Maybe String
  , subscriptionID :: Maybe String
  , timeSubscriptionBooked :: Maybe String  -- ISO timestamp
  }

-- | Workspace with billing info
type WorkspaceWithBilling =
  { id :: String
  , name :: String
  , slug :: String
  , billing :: WorkspaceBilling
  }

-- | Success data after subscription
type SuccessData =
  { plan :: String
  , paymentMethodType :: String
  , paymentMethodLast4 :: Maybe String
  }

-- | Setup intent result
data SetupIntentResult
  = SetupIntentSuccess { clientSecret :: String }
  | SetupIntentError { error :: String }

derive instance eqSetupIntentResult :: Eq SetupIntentResult

-- | Subscribe state
type SubscribeState =
  { planId :: PlanId
  , workspaces :: Array WorkspaceWithBilling
  , selectedWorkspace :: Maybe String
  , success :: Maybe SuccessData
  , failure :: Maybe String
  , clientSecret :: Maybe String
  , loading :: Boolean
  }

-- | Initial state
initialState :: PlanId -> SubscribeState
initialState planId =
  { planId
  , workspaces: []
  , selectedWorkspace: Nothing
  , success: Nothing
  , failure: Nothing
  , clientSecret: Nothing
  , loading: true
  }

-- | Subscribe actions
data SubscribeAction
  = SetWorkspaces (Array WorkspaceWithBilling)
  | SelectWorkspace String
  | SetSuccess SuccessData
  | SetFailure String
  | SetClientSecret String
  | SetLoading Boolean

derive instance eqSubscribeAction :: Eq SubscribeAction

-- | State reducer (pure)
reducer :: SubscribeState -> SubscribeAction -> SubscribeState
reducer state action = case action of
  SetWorkspaces workspaces ->
    let
      autoSelected = if length workspaces == 1 then map _.id (head workspaces) else Nothing
    in
      state { workspaces = workspaces, selectedWorkspace = autoSelected, loading = false }
  
  SelectWorkspace id ->
    state { selectedWorkspace = Just id }
  
  SetSuccess data' ->
    state { success = Just data' }
  
  SetFailure msg ->
    state { failure = Just msg }
  
  SetClientSecret secret ->
    state { clientSecret = Just secret }
  
  SetLoading loading ->
    state { loading = loading }

-- | Validate plan ID string
validatePlan :: String -> Either String PlanId
validatePlan str = case str of
  "20" -> Right Plan20
  "100" -> Right Plan100
  "200" -> Right Plan200
  _ -> Left "Invalid plan ID"

-- | Should show workspace picker modal
shouldShowWorkspacePicker :: SubscribeState -> Boolean
shouldShowWorkspacePicker state =
  length state.workspaces > 1 && isNothing state.selectedWorkspace

-- | Check if workspace has existing subscription
hasExistingSubscription :: WorkspaceWithBilling -> Boolean
hasExistingSubscription ws = case ws.billing.subscriptionID of
  Just _ -> true
  Nothing -> false

-- | Check if workspace has payment method
hasPaymentMethod :: WorkspaceWithBilling -> Boolean
hasPaymentMethod ws = case ws.billing.paymentMethodID of
  Just _ -> true
  Nothing -> false

-- | Booking request data
type BookingRequest =
  { workspaceID :: String
  , plan :: PlanId
  , paymentMethodID :: String
  , paymentMethodType :: String
  , paymentMethodLast4 :: Maybe String
  }

-- | Build booking request (pure)
buildBookingRequest 
  :: String 
  -> PlanId 
  -> { id :: String, type' :: String, last4 :: Maybe String }
  -> BookingRequest
buildBookingRequest workspaceId plan pm =
  { workspaceID: workspaceId
  , plan
  , paymentMethodID: pm.id
  , paymentMethodType: pm.type'
  , paymentMethodLast4: pm.last4
  }

-- | Subscribe result
data SubscribeResult
  = SubscribeSuccess SuccessData
  | SubscribeRedirect String
  | SubscribeError String

derive instance eqSubscribeResult :: Eq SubscribeResult

instance showSubscribeResult :: Show SubscribeResult where
  show (SubscribeSuccess _) = "SubscribeSuccess"
  show (SubscribeRedirect url) = "(SubscribeRedirect " <> show url <> ")"
  show (SubscribeError msg) = "(SubscribeError " <> show msg <> ")"

-- | Stripe Elements appearance config (pure data)
type StripeAppearance =
  { theme :: String
  , colorPrimary :: String
  , colorBackground :: String
  , colorText :: String
  , colorTextSecondary :: String
  , colorDanger :: String
  , fontFamily :: String
  , borderRadius :: String
  }

defaultStripeAppearance :: StripeAppearance
defaultStripeAppearance =
  { theme: "night"
  , colorPrimary: "#ffffff"
  , colorBackground: "#1a1a1a"
  , colorText: "#ffffff"
  , colorTextSecondary: "#999999"
  , colorDanger: "#ff6b6b"
  , fontFamily: "JetBrains Mono, monospace"
  , borderRadius: "4px"
  }
