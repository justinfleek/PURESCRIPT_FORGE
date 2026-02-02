-- | Balance Tracker Component - Comprehensive Token Balance Display
-- |
-- | **What:** Displays token balance information across all providers, with special support
-- |         for Venice Diem system. Shows balances, consumption rates, cost metrics, progress
-- |         bars, and countdown timers.
-- | **Why:** Provides users with real-time visibility into their token usage, costs, and
-- |         remaining balance. Critical for budget management and usage tracking.
-- | **How:** Renders balance widgets with provider selection, displays Venice Diem with
-- |         countdown timer, shows consumption rates and projections, and provides alert
-- |         indicators.
-- |
-- | Coeffect Equation:
-- |   BalanceTracker : Input -> Component Query Input Output m
-- |   with tracking: Balance -o AlertLevel -o Notification
-- |
-- | Module Structure:
-- |   BalanceTracker.Types   - Type definitions
-- |   BalanceTracker.Render  - Rendering functions
-- |   BalanceTracker.Handler - Action and query handling
-- |
-- | Based on spec 51-DIEM-TRACKER-WIDGET.md
module Sidepanel.Components.Balance.BalanceTracker
  ( -- * Component
    component
    -- * Re-exports from Types
  , module Sidepanel.Components.Balance.BalanceTracker.Types
  ) where

import Prelude
import Halogen as H
import Effect.Aff.Class (class MonadAff)
import Data.Maybe (Maybe(..))

-- Re-export types
import Sidepanel.Components.Balance.BalanceTracker.Types
  ( DisplayMode(..)
  , State
  , AnimationState(..)
  , TooltipTarget(..)
  , Input
  , Output(..)
  , Action(..)
  , Query(..)
  , initialState
  , getFlkBalance
  )

-- Internal imports
import Sidepanel.Components.Balance.BalanceTracker.Render (render)
import Sidepanel.Components.Balance.BalanceTracker.Handler (handleAction, handleQuery)

--------------------------------------------------------------------------------
-- | Component
--------------------------------------------------------------------------------

-- | Balance tracker component
-- |
-- | Displays token balance information with provider selection,
-- | consumption rates, progress bars, and alert indicators.
component :: forall m. MonadAff m => H.Component Query Input Output m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , handleQuery = handleQuery
      , receive = Just <<< ReceiveInput
      , initialize = Just Initialize
      }
  }
