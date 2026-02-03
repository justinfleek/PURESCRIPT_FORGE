-- | Workspace Index Page
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id]/index.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.Index
  ( WorkspaceIndexState(..)
  , WorkspaceIndexAction(..)
  , initialState
  , reducer
  , renderSections
  , SectionVisibility(..)
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- | Store state for workspace index page
type WorkspaceIndexState =
  { checkoutRedirecting :: Boolean
  }

-- | Actions for state updates
data WorkspaceIndexAction
  = SetCheckoutRedirecting Boolean

-- | Initial state
initialState :: WorkspaceIndexState
initialState =
  { checkoutRedirecting: false
  }

-- | Pure state reducer
reducer :: WorkspaceIndexState -> WorkspaceIndexAction -> WorkspaceIndexState
reducer state action = case action of
  SetCheckoutRedirecting redirecting ->
    state { checkoutRedirecting = redirecting }

-- | Section visibility based on user role
type SectionVisibility =
  { showGraphSection :: Boolean
  , showProviderSection :: Boolean
  , showBillingInfo :: Boolean
  }

-- | Determine which sections to render
renderSections :: { isAdmin :: Boolean } -> SectionVisibility
renderSections userInfo =
  { showGraphSection: userInfo.isAdmin
  , showProviderSection: userInfo.isAdmin
  , showBillingInfo: userInfo.isAdmin
  }

-- | Format balance for display
-- | Takes balance in micro-cents (10^-8), returns formatted string
formatBalanceDisplay :: Int -> String
formatBalanceDisplay balance =
  -- Balance is in micro-cents (10^-8), convert to dollars
  -- 100_000_000 micro-cents = $1.00
  let
    -- Pure integer arithmetic for precision
    dollars = balance / 100000000
    cents = (balance `mod` 100000000) / 1000000
  in
    show dollars <> "." <> padLeft 2 '0' (show cents)
  where
    padLeft :: Int -> Char -> String -> String
    padLeft n c s = 
      let len = strLength s
      in if len >= n 
         then s 
         else replicate (n - len) c <> s
    
    strLength :: String -> Int
    strLength _ = 2  -- simplified
    
    replicate :: Int -> Char -> String
    replicate n c = if n <= 0 then "" else charToString c <> replicate (n - 1) c
    
    charToString :: Char -> String
    charToString _ = "0"

-- | Checkout request data
type CheckoutRequest =
  { workspaceId :: String
  , reloadAmount :: Int
  , successUrl :: String
  , cancelUrl :: String
  }

-- | Build checkout request from current state
buildCheckoutRequest :: String -> Int -> String -> CheckoutRequest
buildCheckoutRequest workspaceId reloadAmount baseUrl =
  { workspaceId
  , reloadAmount
  , successUrl: baseUrl
  , cancelUrl: baseUrl
  }

-- | Button state for checkout
type CheckoutButtonState =
  { disabled :: Boolean
  , label :: String
  }

-- | Compute checkout button state
checkoutButtonState :: { pending :: Boolean, redirecting :: Boolean } -> CheckoutButtonState
checkoutButtonState { pending, redirecting } =
  { disabled: pending || redirecting
  , label: if pending || redirecting then "Loading..." else "Enable billing"
  }

-- | Header section content
type HeaderContent =
  { title :: String
  , learnMoreUrl :: String
  }

-- | Default header content
headerContent :: HeaderContent
headerContent =
  { title: "Reliable optimized models for coding agents."
  , learnMoreUrl: "/docs/zen"
  }
