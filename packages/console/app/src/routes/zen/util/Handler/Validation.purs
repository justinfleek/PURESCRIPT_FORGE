-- | Omega Handler Validation Functions
-- | Pure PureScript validation logic
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/omega/util/handler.ts
-- | Migrated: 2026-02-04
module Console.App.Routes.Omega.Util.Handler.Validation
  ( validateModel
  , validateBilling
  , validateModelSettings
  ) where

import Prelude

import Data.Maybe (Maybe(..), isJust)
import Data.Array (find)
import Data.Either (Either(..))
import Foreign.Object as Object
import Console.App.Routes.Omega.Util.Error (OmegaError(..), ModelError, CreditsError, MonthlyLimitError, UserLimitError, SubscriptionError)
import Console.App.Routes.Omega.Util.Handler.Types (ModelInfo, AuthInfo, BillingSource(..))
import Console.Core.Util.Price (centsToMicroCents)

-- | Free workspaces that don't require billing
freeWorkspaces :: Array String
freeWorkspaces =
  [ "wrk_01K46JDFR0E75SG2Q8K172KF3Y"  -- frank
  , "wrk_01K6W1A3VE0KMNVSCQT43BG2SX"  -- opencode bench
  ]

-- | Omega data structure
type OmegaData =
  { models :: Object.Object (Array ModelInfo)
  }

-- | Validate model is supported for the given format
validateModel ::
  OmegaData ->
  String ->
  String ->  -- format
  Either OmegaError ModelInfo
validateModel omegaData reqModel format =
  case Object.lookup reqModel omegaData.models of
    Nothing -> Left $ ModelError $ "Model " <> reqModel <> " not supported"
    Just modelInfos ->
      case findModelForFormat modelInfos format of
        Nothing -> Left $ ModelError $ "Model " <> reqModel <> " not supported for format " <> format
        Just modelInfo -> Right modelInfo

-- | Find model variant for specific format
findModelForFormat :: Array ModelInfo -> String -> Maybe ModelInfo
findModelForFormat models format =
  find (\m -> case m.formatFilter of
    Just f -> f == format
    Nothing -> true
  ) models

-- | Validate billing and determine billing source
validateBilling ::
  Maybe AuthInfo ->
  ModelInfo ->
  Either OmegaError BillingSource
validateBilling Nothing modelInfo =
  if modelInfo.allowAnonymous
    then Right Anonymous
    else Left $ AuthError "Missing API key."
validateBilling (Just authInfo) modelInfo
  | isJust authInfo.provider = Right Free  -- BYOK provider
  | authInfo.isFree = Right Free
  | modelInfo.allowAnonymous = Right Free
  | otherwise = validateBillingSource authInfo

-- | Validate billing source for authenticated users
validateBillingSource :: AuthInfo -> Either OmegaError BillingSource
validateBillingSource authInfo =
  case authInfo.billing.subscription, authInfo.subscription of
    Just subPlan, Just sub ->
      -- Validate subscription billing
      case validateSubscriptionLimits subPlan sub of
        Left err -> 
          if subPlan.useBalance
            then validatePayAsYouGo authInfo  -- Fall back to balance
            else Left err
        Right _ -> Right Subscription
    _, _ -> validatePayAsYouGo authInfo

-- | Validate subscription limits
validateSubscriptionLimits ::
  { plan :: String, useBalance :: Boolean } ->
  { id :: String
  , rollingUsage :: Maybe MicroCents
  , fixedUsage :: Maybe MicroCents
  , timeRollingUpdated :: Maybe Date
  , timeFixedUpdated :: Maybe Date
  } ->
  Either OmegaError Unit
validateSubscriptionLimits plan sub = do
  -- Check weekly limit (fixed usage)
  case sub.fixedUsage, sub.timeFixedUpdated of
    Just usage, Just timeUpdated ->
      case analyzeWeeklyUsage plan.plan usage timeUpdated of
        { status: "rate-limited", resetInSec } ->
          Left $ SubscriptionError
            ("Subscription quota exceeded. Retry in " <> formatRetryTime resetInSec <> ".")
            (Just resetInSec)
        _ -> pure unit
    _, _ -> pure unit
  
  -- Check rolling limit
  case sub.rollingUsage, sub.timeRollingUpdated of
    Just usage, Just timeUpdated ->
      case analyzeRollingUsage plan.plan usage timeUpdated of
        { status: "rate-limited", resetInSec } ->
          Left $ SubscriptionError
            ("Subscription quota exceeded. Retry in " <> formatRetryTime resetInSec <> ".")
            (Just resetInSec)
        _ -> pure unit
    _, _ -> pure unit
  
  pure unit

-- | Validate pay-as-you-go billing
validatePayAsYouGo :: AuthInfo -> Either OmegaError BillingSource
validatePayAsYouGo authInfo = do
  -- Check payment method
  case authInfo.billing.paymentMethodID of
    Nothing -> Left $ CreditsError $
      "No payment method. Add a payment method here: https://opencode.ai/workspace/" <>
      authInfo.workspaceID <> "/billing"
    Just _ -> pure unit
  
  -- Check balance
  if authInfo.billing.balance <= 0
    then Left $ CreditsError $
      "Insufficient balance. Manage your billing here: https://opencode.ai/workspace/" <>
      authInfo.workspaceID <> "/billing"
    else pure unit
  
  -- Check monthly limit (workspace)
  validateMonthlyLimit
    authInfo.billing.monthlyLimit
    authInfo.billing.monthlyUsage
    authInfo.billing.timeMonthlyUsageUpdated
    authInfo.workspaceID
    true
  
  -- Check monthly limit (user)
  validateMonthlyLimit
    authInfo.user.monthlyLimit
    authInfo.user.monthlyUsage
    authInfo.user.timeMonthlyUsageUpdated
    authInfo.workspaceID
    false
  
  Right Balance

-- | Validate monthly spending limit
validateMonthlyLimit ::
  Maybe Int ->  -- limit in dollars
  Maybe MicroCents ->  -- usage
  Maybe Date ->  -- time updated
  String ->  -- workspace ID
  Boolean ->  -- is workspace (vs user)
  Either OmegaError Unit
validateMonthlyLimit (Just limit) (Just usage) (Just timeUpdated) workspaceId isWorkspace
  | usage >= centsToMicroCents (limit * 100) &&
    isCurrentMonth timeUpdated = do
      let limitMsg = if isWorkspace
            then "Your workspace has reached its monthly spending limit of $" <> show limit <>
                 ". Manage your limits here: https://opencode.ai/workspace/" <> workspaceId <> "/billing"
            else "You have reached your monthly spending limit of $" <> show limit <>
                 ". Manage your limits here: https://opencode.ai/workspace/" <> workspaceId <> "/members"
      Left $ if isWorkspace
        then MonthlyLimitError limitMsg
        else UserLimitError limitMsg
  | otherwise = Right unit
validateMonthlyLimit _ _ _ _ _ = Right unit

-- | Validate model settings
validateModelSettings :: Maybe AuthInfo -> Either OmegaError Unit
validateModelSettings Nothing = Right unit
validateModelSettings (Just authInfo)
  | authInfo.isDisabled = Left $ ModelError "Model is disabled"
  | otherwise = Right unit

-- | Format retry time for display
formatRetryTime :: Int -> String
formatRetryTime seconds
  | seconds >= 86400 =
      let days = seconds / 86400
      in show days <> (if days > 1 then " days" else " day")
  | seconds >= 3600 =
      let
        hours = seconds / 3600
        minutes = (seconds `mod` 3600) / 60
      in
        show hours <> "hr " <> show minutes <> "min"
  | otherwise =
      let minutes = (seconds + 59) / 60  -- ceiling
      in show minutes <> "min"

-- | Analyze weekly usage (FFI - calls Black.analyzeWeeklyUsage)
foreign import analyzeWeeklyUsage ::
  String ->  -- plan
  MicroCents ->  -- usage
  Date ->  -- timeUpdated
  { status :: String, resetInSec :: Int }

-- | Analyze rolling usage (FFI - calls Black.analyzeRollingUsage)
foreign import analyzeRollingUsage ::
  String ->  -- plan
  MicroCents ->  -- usage
  Date ->  -- timeUpdated
  { status :: String, resetInSec :: Int }

-- | Check if date is in current month (FFI)
foreign import isCurrentMonth :: Date -> Boolean

-- | FFI imports from FFI.js
foreign import analyzeWeeklyUsageImpl :: String -> Int -> Foreign -> Foreign
foreign import analyzeRollingUsageImpl :: String -> Int -> Foreign -> Foreign
foreign import isCurrentMonthImpl :: Foreign -> Boolean
