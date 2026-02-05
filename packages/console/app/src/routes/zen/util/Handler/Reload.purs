-- | Omega Handler Reload Logic
-- | Pure PureScript reload logic (DB operations as FFI)
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/handler.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.Util.Handler.Reload
  ( shouldReload
  , checkReload
  ) where

import Prelude

import Effect.Aff (Aff)
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Console.App.Routes.Omega.Util.Handler.Types (AuthInfo, CostInfo, Date)
import Console.Core.Util.Price (MicroCents, centsToMicroCents)

-- | Default reload trigger (in dollars)
defaultReloadTrigger :: Int
defaultReloadTrigger = 5  -- $5

-- | Check if reload should be triggered
shouldReload ::
  AuthInfo ->
  CostInfo ->
  Boolean
shouldReload authInfo costInfo
  | authInfo.isFree = false
  | isJust authInfo.provider = false  -- BYOK
  | isJust authInfo.subscription = false  -- Subscription
  | otherwise = checkBalanceThreshold authInfo costInfo

-- | Check if balance is below reload threshold
checkBalanceThreshold :: AuthInfo -> CostInfo -> Boolean
checkBalanceThreshold authInfo costInfo =
  let
    reloadTrigger = centsToMicroCents $
      (fromMaybe defaultReloadTrigger authInfo.billing.reloadTrigger) * 100
    newBalance = authInfo.billing.balance - costInfo.costInMicroCents
  in
    newBalance < reloadTrigger &&
    not (isReloadLocked authInfo)

-- | Check if reload is currently locked
isReloadLocked :: AuthInfo -> Boolean
isReloadLocked authInfo =
  case authInfo.billing.timeReloadLockedTill of
    Just lockedTill -> isDateInFuture lockedTill
    Nothing -> false

-- | Attempt to acquire reload lock and trigger reload
checkReload ::
  AuthInfo ->
  CostInfo ->
  Aff Boolean  -- true if reload was triggered
checkReload authInfo costInfo =
  if shouldReload authInfo costInfo
    then do
      -- Try to acquire lock (FFI boundary - pure PureScript types)
      lockAcquired <- acquireReloadLock authInfo
      if lockAcquired
        then do
          -- Trigger reload via FFI (Actor boundary)
          triggerReload authInfo.workspaceID
          pure true
        else pure false
    else pure false

-- | Acquire reload lock (FFI boundary - DB operation)
-- | Takes pure PureScript AuthInfo, converts to Foreign internally
foreign import acquireReloadLock :: AuthInfo -> Aff Boolean

-- | Trigger reload (FFI boundary - calls Billing.reload via Actor)
foreign import triggerReload :: String -> Aff Unit

-- | Check if date is in future (FFI boundary - system time)
-- | Takes pure PureScript Date, converts to Foreign internally
foreign import isDateInFuture :: Date -> Boolean
