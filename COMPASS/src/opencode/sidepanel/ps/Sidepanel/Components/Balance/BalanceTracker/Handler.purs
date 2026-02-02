-- | BalanceTracker Handler
-- |
-- | Action and query handling for the balance tracker component.
-- |
-- | Coeffect Equation:
-- |   Handler : Action -> H.HalogenM State Action () Output m Unit
-- |   with alerts: Balance -> AlertLevel -> Output
-- |
-- | Module Coverage: handleAction, handleQuery
module Sidepanel.Components.Balance.BalanceTracker.Handler
  ( handleAction
  , handleQuery
  ) where

import Prelude
import Halogen as H
import Effect.Aff.Class (class MonadAff)
import Control.Monad.State.Class (class MonadState)
import Data.Maybe (Maybe(..))
import Sidepanel.State.Balance (AlertLevel(..), calculateAlertLevel)
import Sidepanel.Components.Balance.BalanceTracker.Types
  ( State
  , Action(..)
  , Query(..)
  , Output(..)
  , DisplayMode(..)
  , AnimationState(..)
  )

--------------------------------------------------------------------------------
-- | Action Handler
--------------------------------------------------------------------------------

-- | Handle component actions
handleAction :: forall m. MonadAff m => Action -> H.HalogenM State Action () Output m Unit
handleAction = case _ of
  Initialize -> pure unit

  ReceiveInput { balance, countdown, selectedProvider } -> do
    let newAlertLevel = calculateAlertLevel balance
    oldState <- H.get
    
    when (newAlertLevel /= oldState.alertLevel) do
      H.raise $ AlertTriggered newAlertLevel
      H.modify_ _ { animationState = case newAlertLevel of
          Critical -> Pulsing
          Depleted -> Pulsing
          Warning -> Fading
          Normal -> Idle
        }
    
    displayMode <- case selectedProvider of
      Just "venice" -> pure VeniceOnly
      Just "flk" -> pure FlkOnly
      Just pid -> pure (Provider pid)
      Nothing -> pure AllProviders
    
    H.modify_ _ { balance = balance, countdown = countdown, alertLevel = newAlertLevel, displayMode = displayMode }

  SetDisplayMode mode -> do
    H.modify_ _ { displayMode = mode }
    case mode of
      Provider pid -> H.raise (ProviderSelected pid)
      _ -> pure unit

  ToggleExpanded ->
    H.modify_ \s -> s { expanded = not s.expanded }

  ShowTooltip target ->
    H.modify_ _ { showTooltip = Just target }

  HideTooltip ->
    H.modify_ _ { showTooltip = Nothing }

  OpenSettings ->
    H.raise SettingsRequested

  RefreshBalance ->
    H.raise RefreshRequested

  CountdownTick -> pure unit

--------------------------------------------------------------------------------
-- | Query Handler
--------------------------------------------------------------------------------

-- | Handle parent queries
handleQuery :: forall m a. MonadAff m => Query a -> H.HalogenM State Action () Output m (Maybe a)
handleQuery = case _ of
  GetAlertLevel k -> do
    state <- H.get
    pure $ Just (k state.alertLevel)

  ForceRefresh k -> do
    H.raise RefreshRequested
    pure (Just k)

  SetBalance balance k -> do
    H.modify_ _ { balance = balance, alertLevel = calculateAlertLevel balance }
    pure (Just k)
