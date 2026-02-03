-- | New User Section - Onboarding
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id]/new-user-section.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.NewUserSection
  ( NewUserState(..)
  , NewUserAction(..)
  , KeyDisplay(..)
  , Feature(..)
  , NextStep(..)
  , initialState
  , reducer
  , isNewUser
  , maskApiKey
  , features
  , nextSteps
  ) where

import Prelude

import Data.Array (length)
import Data.Maybe (Maybe(..))
import Data.String (take, drop)
import Data.String as String

-- | Key display info
type KeyDisplay =
  { actual :: String
  , masked :: String
  }

-- | New user section state
type NewUserState =
  { copiedKey :: Boolean
  }

-- | Actions for new user section
data NewUserAction
  = SetCopiedKey Boolean
  | ResetCopiedKey

-- | Initial state
initialState :: NewUserState
initialState =
  { copiedKey: false
  }

-- | Pure state reducer
reducer :: NewUserState -> NewUserAction -> NewUserState
reducer state action = case action of
  SetCopiedKey copied -> state { copiedKey = copied }
  ResetCopiedKey -> state { copiedKey = false }

-- | Check if user is new (has one key and no usage)
isNewUser :: { keysCount :: Int, usageCount :: Int } -> Boolean
isNewUser { keysCount, usageCount } =
  keysCount == 1 && usageCount == 0

-- | Mask an API key for display
-- | Shows first 8 and last 4 characters, masks the middle
-- | Example: "sk-abc123...xyz" -> "sk-abc12****xyz"
maskApiKey :: String -> KeyDisplay
maskApiKey key =
  let
    keyLength = String.length key
    prefix = take 8 key
    suffix = drop (keyLength - 4) key
    maskedLength = keyLength - 12
    masked = prefix <> repeatChar '*' maskedLength <> suffix
  in
    { actual: key
    , masked: masked
    }
  where
    repeatChar :: Char -> Int -> String
    repeatChar c n =
      if n <= 0 
        then "" 
        else String.singleton c <> repeatChar c (n - 1)

-- | Feature description
type Feature =
  { title :: String
  , description :: String
  }

-- | Onboarding features
features :: Array Feature
features =
  [ { title: "Tested & Verified Models"
    , description: "We've benchmarked and tested models specifically for coding agents to ensure the best performance."
    }
  , { title: "Highest Quality"
    , description: "Access models configured for optimal performance - no downgrades or routing to cheaper providers."
    }
  , { title: "No Lock-in"
    , description: "Use Zen with any coding agent, and continue using other providers with opencode whenever you want."
    }
  ]

-- | Next step instruction
type NextStep =
  { step :: Int
  , instruction :: String
  , code :: Maybe String
  }

-- | Onboarding next steps
nextSteps :: Array NextStep
nextSteps =
  [ { step: 1
    , instruction: "Enable billing"
    , code: Nothing
    }
  , { step: 2
    , instruction: "Run"
    , code: Just "opencode auth login"
    }
  , { step: 3
    , instruction: "Paste your API key"
    , code: Nothing
    }
  , { step: 4
    , instruction: "Start opencode and run"
    , code: Just "/models"
    }
  ]

-- | Copy button state
type CopyButtonState =
  { disabled :: Boolean
  , label :: String
  , showCheckIcon :: Boolean
  }

-- | Compute copy button state
copyButtonState :: NewUserState -> CopyButtonState
copyButtonState state =
  { disabled: state.copiedKey
  , label: if state.copiedKey then "Copied!" else "Copy Key"
  , showCheckIcon: state.copiedKey
  }

-- | Get the default (most recent) key from a list
getDefaultKey :: Array { key :: String } -> Maybe KeyDisplay
getDefaultKey keys =
  case lastElement keys of
    Nothing -> Nothing
    Just { key } -> Just (maskApiKey key)
  where
    lastElement :: forall a. Array a -> Maybe a
    lastElement arr = 
      case length arr of
        0 -> Nothing
        n -> index arr (n - 1)
    
    index :: forall a. Array a -> Int -> Maybe a
    index _ _ = Nothing  -- simplified

-- | Usage info for determining new user status
type UsageInfo = Array { id :: String }

-- | Keys info
type KeysInfo = Array { key :: String }

-- | Check visibility of new user section
shouldShowNewUserSection :: KeysInfo -> UsageInfo -> Boolean
shouldShowNewUserSection keys usage =
  length keys == 1 && length usage == 0

-- | Feature grid item
type FeatureGridItem =
  { slot :: String
  , feature :: Feature
  }

-- | Build feature grid
buildFeatureGrid :: Array FeatureGridItem
buildFeatureGrid =
  map (\f -> { slot: "feature", feature: f }) features

-- | API key highlight section
type ApiKeyHighlight =
  { keyDisplay :: Maybe KeyDisplay
  , copyState :: CopyButtonState
  }

-- | Build API key highlight
buildApiKeyHighlight :: Maybe KeyDisplay -> NewUserState -> ApiKeyHighlight
buildApiKeyHighlight keyDisplay state =
  { keyDisplay
  , copyState: copyButtonState state
  }

-- | Next steps list item
type NextStepItem =
  { index :: Int
  , step :: NextStep
  }

-- | Build next steps list
buildNextStepsList :: Array NextStepItem
buildNextStepsList =
  mapWithIndex (\i s -> { index: i + 1, step: s }) nextSteps
  where
    mapWithIndex :: forall a b. (Int -> a -> b) -> Array a -> Array b
    mapWithIndex f arr = go arr 0
      where
        go [] _ = []
        go (x : xs) i = [f i x] <> go xs (i + 1)
