-- | Black Index Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/black/index.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Black.Index
  ( BlackPageState(..)
  , BlackPageAction(..)
  , TermsItem
  , initialState
  , reducer
  , subscribeTerms
  , buildSubscribeUrl
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Console.App.Routes.Black.Common (PlanId(..), Plan, plans, getPlanById)

-- | Page state
type BlackPageState =
  { selectedPlan :: Maybe PlanId
  , mounted :: Boolean
  }

-- | Initial state
initialState :: Maybe String -> BlackPageState
initialState planParam =
  { selectedPlan: parsePlanParam planParam
  , mounted: false
  }
  where
    parsePlanParam :: Maybe String -> Maybe PlanId
    parsePlanParam Nothing = Nothing
    parsePlanParam (Just "20") = Just Plan20
    parsePlanParam (Just "100") = Just Plan100
    parsePlanParam (Just "200") = Just Plan200
    parsePlanParam (Just _) = Nothing

-- | Page actions
data BlackPageAction
  = SelectPlan PlanId
  | CancelSelection
  | SetMounted

derive instance eqBlackPageAction :: Eq BlackPageAction

instance showBlackPageAction :: Show BlackPageAction where
  show (SelectPlan p) = "(SelectPlan " <> show p <> ")"
  show CancelSelection = "CancelSelection"
  show SetMounted = "SetMounted"

-- | State reducer (pure)
reducer :: BlackPageState -> BlackPageAction -> BlackPageState
reducer state action = case action of
  SelectPlan planId ->
    state { selectedPlan = Just planId }
  
  CancelSelection ->
    state { selectedPlan = Nothing }
  
  SetMounted ->
    state { mounted = true }

-- | Terms items for subscription
type TermsItem = String

subscribeTerms :: Array TermsItem
subscribeTerms =
  [ "Your subscription will not start immediately"
  , "You will be added to the waitlist and activated soon"
  , "Your card will be only charged when your subscription is activated"
  , "Usage limits apply, heavily automated use may reach limits sooner"
  , "Subscriptions for individuals, contact Enterprise for teams"
  , "Limits may be adjusted and plans may be discontinued in the future"
  , "Cancel your subscription at anytime"
  ]

-- | Build subscribe URL for plan
buildSubscribeUrl :: PlanId -> String
buildSubscribeUrl planId = "/black/subscribe/" <> show planId

-- | Fine print text
finePrintText :: String
finePrintText = "Prices shown don't include applicable tax"

-- | Format price for display
formatPrice :: Int -> String
formatPrice price = "$" <> show price

-- | Format period text
formatPeriod :: String
formatPeriod = "per month"

-- | Format selected period text
formatSelectedPeriod :: String
formatSelectedPeriod = "per person billed monthly"

-- | View transition name for card
cardTransitionName :: PlanId -> String
cardTransitionName planId = "card-" <> show planId

-- | View transition name for terms
termsTransitionName :: PlanId -> String
termsTransitionName planId = "terms-" <> show planId

-- | View transition name for actions
actionsTransitionName :: PlanId -> String
actionsTransitionName planId = "actions-" <> show planId
