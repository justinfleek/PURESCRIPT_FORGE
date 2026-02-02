-- | BalanceTracker Types
-- |
-- | Type definitions for the balance tracker component.
-- |
-- | Coeffect Equation:
-- |   Types : DisplayMode * AlertLevel * AnimationState -> State
-- |   with tracking: Balance -o Alert
-- |
-- | Module Coverage: DisplayMode, State, Action, Query, Output, TooltipTarget
module Sidepanel.Components.Balance.BalanceTracker.Types
  ( -- * Display Mode
    DisplayMode(..)
    -- * State
  , State
  , AnimationState(..)
  , TooltipTarget(..)
    -- * Input/Output
  , Input
  , Output(..)
    -- * Actions
  , Action(..)
    -- * Queries
  , Query(..)
    -- * Initial State
  , initialState
    -- * Helpers
  , getFlkBalance
  ) where

import Prelude
import Data.Maybe (Maybe(..))
import Sidepanel.State.Balance (BalanceState, FlkBalance, AlertLevel, calculateAlertLevel)
import Sidepanel.Utils.Time (TimeRemaining)

--------------------------------------------------------------------------------
-- | Display Mode
--------------------------------------------------------------------------------

-- | Display mode
data DisplayMode
  = AllProviders      -- Show aggregated across all providers
  | Provider String   -- Show specific provider
  | VeniceOnly        -- Show Venice Diem system
  | FlkOnly           -- Show Fleek Token (FLK) balance

derive instance eqDisplayMode :: Eq DisplayMode

--------------------------------------------------------------------------------
-- | Animation State
--------------------------------------------------------------------------------

data AnimationState = Idle | Pulsing | Fading

derive instance eqAnimationState :: Eq AnimationState

--------------------------------------------------------------------------------
-- | Tooltip Target
--------------------------------------------------------------------------------

data TooltipTarget
  = BalanceTooltip
  | TokenTooltip
  | CostTooltip
  | RateTooltip
  | ProjectionTooltip
  | ProgressTooltip
  | CountdownTooltip
  | ProviderTooltip

derive instance eqTooltipTarget :: Eq TooltipTarget

--------------------------------------------------------------------------------
-- | Input/Output
--------------------------------------------------------------------------------

-- | Component input
type Input =
  { balance :: BalanceState
  , countdown :: TimeRemaining
  , selectedProvider :: Maybe String
  }

-- | Component output
data Output
  = AlertTriggered AlertLevel
  | SettingsRequested
  | RefreshRequested
  | ProviderSelected String

--------------------------------------------------------------------------------
-- | State
--------------------------------------------------------------------------------

-- | Internal state
type State =
  { balance :: BalanceState
  , countdown :: TimeRemaining
  , displayMode :: DisplayMode
  , expanded :: Boolean
  , alertLevel :: AlertLevel
  , showTooltip :: Maybe TooltipTarget
  , animationState :: AnimationState
  }

--------------------------------------------------------------------------------
-- | Actions
--------------------------------------------------------------------------------

-- | Internal actions
data Action
  = Initialize
  | ReceiveInput Input
  | SetDisplayMode DisplayMode
  | ToggleExpanded
  | ShowTooltip TooltipTarget
  | HideTooltip
  | OpenSettings
  | RefreshBalance
  | CountdownTick

--------------------------------------------------------------------------------
-- | Queries
--------------------------------------------------------------------------------

-- | Queries from parent
data Query a
  = GetAlertLevel (AlertLevel -> a)
  | ForceRefresh a
  | SetBalance BalanceState a

--------------------------------------------------------------------------------
-- | Initial State
--------------------------------------------------------------------------------

-- | Initialize state from input
initialState :: Input -> State
initialState { balance, countdown, selectedProvider } =
  { balance
  , countdown
  , displayMode: case selectedProvider of
      Just "venice" -> VeniceOnly
      Just "flk" -> FlkOnly
      Just pid -> Provider pid
      Nothing -> AllProviders
  , expanded: false
  , alertLevel: calculateAlertLevel balance
  , showTooltip: Nothing
  , animationState: Idle
  }

--------------------------------------------------------------------------------
-- | Helpers
--------------------------------------------------------------------------------

-- | Get FLK balance from BalanceState
getFlkBalance :: BalanceState -> Maybe FlkBalance
getFlkBalance balance = balance.flk
