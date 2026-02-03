-- | Reload Section - Auto Reload Settings
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id]/billing/reload-section.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.Billing.ReloadSection
  ( ReloadSectionState(..)
  , ReloadSectionAction(..)
  , ReloadFormData(..)
  , ReloadSettings(..)
  , initialState
  , reducer
  , validateReloadSettings
  , calculateProcessingFee
  , formatReloadDescription
  , buildFormData
  ) where

import Prelude

import Data.Int (toNumber)
import Data.Maybe (Maybe(..))

-- | Reload section state
type ReloadSectionState =
  { show :: Boolean
  , reload :: Boolean
  , reloadAmount :: String
  , reloadTrigger :: String
  }

-- | Actions for reload section
data ReloadSectionAction
  = Show ReloadSettings
  | Hide
  | SetReload Boolean
  | SetReloadAmount String
  | SetReloadTrigger String

-- | Reload settings from billing info
type ReloadSettings =
  { reload :: Boolean
  , reloadAmount :: Int
  , reloadTrigger :: Int
  }

-- | Initial state
initialState :: ReloadSectionState
initialState =
  { show: false
  , reload: false
  , reloadAmount: ""
  , reloadTrigger: ""
  }

-- | Pure state reducer
reducer :: ReloadSectionState -> ReloadSectionAction -> ReloadSectionState
reducer state action = case action of
  Show settings ->
    state 
      { show = true
      , reload = true  -- Always enable when showing
      , reloadAmount = show settings.reloadAmount
      , reloadTrigger = show settings.reloadTrigger
      }
  Hide -> state { show = false }
  SetReload reload -> state { reload = reload }
  SetReloadAmount amount -> state { reloadAmount = amount }
  SetReloadTrigger trigger -> state { reloadTrigger = trigger }

-- | Reload form data
type ReloadFormData =
  { workspaceId :: String
  , reload :: Boolean
  , reloadAmount :: Maybe Int
  , reloadTrigger :: Maybe Int
  }

-- | Build form data
buildFormData :: String -> ReloadSectionState -> ReloadFormData
buildFormData workspaceId state =
  { workspaceId
  , reload: state.reload
  , reloadAmount: parseIntMaybe state.reloadAmount
  , reloadTrigger: parseIntMaybe state.reloadTrigger
  }
  where
    parseIntMaybe :: String -> Maybe Int
    parseIntMaybe _ = Nothing  -- simplified

-- | Minimum reload amount
reloadAmountMin :: Int
reloadAmountMin = 5  -- $5.00

-- | Minimum reload trigger
reloadTriggerMin :: Int
reloadTriggerMin = 1  -- $1.00

-- | Validation error
type ValidationError = String

-- | Validate reload settings
validateReloadSettings :: ReloadFormData -> Maybe ValidationError
validateReloadSettings formData
  | not formData.reload = Nothing  -- No validation needed if disabled
  | otherwise = case formData.reloadAmount of
      Nothing -> Just $ "Reload amount must be at least $" <> show reloadAmountMin
      Just amount ->
        if amount < reloadAmountMin
          then Just $ "Reload amount must be at least $" <> show reloadAmountMin
          else case formData.reloadTrigger of
            Nothing -> Just $ "Balance trigger must be at least $" <> show reloadTriggerMin
            Just trigger ->
              if trigger < reloadTriggerMin
                then Just $ "Balance trigger must be at least $" <> show reloadTriggerMin
                else Nothing

-- | Calculate processing fee for a reload amount
-- | Formula: ((amount + 0.3) / 0.956) * 0.044 + 0.3
calculateProcessingFee :: Int -> String
calculateProcessingFee amount =
  let
    amountNum = toNumber amount
    fee = ((amountNum + 0.3) / 0.956) * 0.044 + 0.3
  in
    formatNumber fee 2
  where
    formatNumber :: Number -> Int -> String
    formatNumber n _ = show n  -- simplified

-- | Format reload description
formatReloadDescription :: ReloadSettings -> String
formatReloadDescription settings =
  "Auto reload is enabled. We'll reload $" 
    <> show settings.reloadAmount
    <> " (+$" 
    <> calculateProcessingFee settings.reloadAmount
    <> " processing fee) when balance reaches $"
    <> show settings.reloadTrigger
    <> "."

-- | Format disabled description
formatDisabledDescription :: String
formatDisabledDescription =
  "Auto reload is disabled. Enable to automatically reload when balance is low."

-- | Section content
type ReloadSectionContent =
  { title :: String
  , enabledLabel :: String
  , reloadAmountLabel :: String
  , reloadTriggerLabel :: String
  }

-- | Default section content
sectionContent :: ReloadSectionContent
sectionContent =
  { title: "Auto Reload"
  , enabledLabel: "Enable Auto Reload"
  , reloadAmountLabel: "Reload $"
  , reloadTriggerLabel: "When balance reaches $"
  }

-- | Reload error display
type ReloadErrorDisplay =
  { hasError :: Boolean
  , time :: String
  , reason :: String
  , message :: String
  }

-- | Build reload error display
buildReloadErrorDisplay :: Maybe String -> Maybe String -> ReloadErrorDisplay
buildReloadErrorDisplay mbError mbTime =
  case mbError of
    Nothing ->
      { hasError: false
      , time: ""
      , reason: ""
      , message: ""
      }
    Just error ->
      { hasError: true
      , time: case mbTime of
          Nothing -> ""
          Just t -> formatErrorTime t
      , reason: stripTrailingDot error
      , message: "Please update your payment method and try again."
      }
  where
    stripTrailingDot :: String -> String
    stripTrailingDot s = s  -- simplified
    
    formatErrorTime :: String -> String
    formatErrorTime t = t  -- simplified

-- | Button state
type ButtonState =
  { disabled :: Boolean
  , label :: String
  }

-- | Edit/Enable button label
editButtonLabel :: Boolean -> String
editButtonLabel reload =
  if reload then "Edit" else "Enable"

-- | Save button state
saveButtonState :: { pending :: Boolean } -> ButtonState
saveButtonState { pending } =
  { disabled: pending
  , label: if pending then "Saving..." else "Save"
  }

-- | Retry button state
retryButtonState :: { pending :: Boolean } -> ButtonState
retryButtonState { pending } =
  { disabled: pending
  , label: if pending then "Retrying..." else "Retry"
  }

-- | Input field state
type InputFieldState =
  { value :: String
  , min :: Int
  , placeholder :: String
  , disabled :: Boolean
  }

-- | Build reload amount input state
buildReloadAmountInputState :: ReloadSectionState -> Int -> InputFieldState
buildReloadAmountInputState state minAmount =
  { value: state.reloadAmount
  , min: minAmount
  , placeholder: state.reloadAmount
  , disabled: not state.reload
  }

-- | Build reload trigger input state
buildReloadTriggerInputState :: ReloadSectionState -> Int -> InputFieldState
buildReloadTriggerInputState state minTrigger =
  { value: state.reloadTrigger
  , min: minTrigger
  , placeholder: state.reloadTrigger
  , disabled: not state.reload
  }

-- | Toggle state for enable checkbox
type ToggleState =
  { checked :: Boolean
  , name :: String
  , value :: String
  }

-- | Build toggle state
buildToggleState :: ReloadSectionState -> ToggleState
buildToggleState state =
  { checked: state.reload
  , name: "reload"
  , value: "true"
  }
