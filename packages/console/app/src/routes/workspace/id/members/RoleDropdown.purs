-- | Role Dropdown Component
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id]/members/role-dropdown.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.Members.RoleDropdown
  ( RoleDropdownState(..)
  , RoleDropdownAction(..)
  , RoleOption(..)
  , initialState
  , reducer
  , roleOptions
  ) where

import Prelude

import Data.Array (filter) as Array

-- | Role option
type RoleOption =
  { value :: String
  , description :: String
  }

-- | Role dropdown state
type RoleDropdownState =
  { open :: Boolean
  , selectedValue :: String
  }

-- | Actions for role dropdown
data RoleDropdownAction
  = Open
  | Close
  | Toggle
  | Select String

-- | Initial state
initialState :: String -> RoleDropdownState
initialState value =
  { open: false
  , selectedValue: value
  }

-- | Pure state reducer
reducer :: RoleDropdownState -> RoleDropdownAction -> RoleDropdownState
reducer state action = case action of
  Open -> state { open = true }
  Close -> state { open = false }
  Toggle -> state { open = not state.open }
  Select value -> state { selectedValue = value, open = false }

-- | Available role options
roleOptions :: Array RoleOption
roleOptions =
  [ { value: "admin", description: "Can manage models, members, and billing" }
  , { value: "member", description: "Can only generate API keys for themselves" }
  ]

-- | Check if option is selected
isSelected :: String -> String -> Boolean
isSelected currentValue optionValue = currentValue == optionValue

-- | Get role description by value
getRoleDescription :: String -> String
getRoleDescription value =
  case Array.filter (\opt -> opt.value == value) roleOptions of
    [opt] -> opt.description
    _ -> ""

-- | Dropdown trigger display
type TriggerDisplay =
  { label :: String
  }

-- | Build trigger display
buildTriggerDisplay :: String -> TriggerDisplay
buildTriggerDisplay value =
  { label: value
  }

-- | Option display
type OptionDisplay =
  { value :: String
  , label :: String
  , description :: String
  , isSelected :: Boolean
  }

-- | Build option displays
buildOptionDisplays :: String -> Array OptionDisplay
buildOptionDisplays selectedValue =
  map (buildOption selectedValue) roleOptions

-- | Build single option display
buildOption :: String -> RoleOption -> OptionDisplay
buildOption selectedValue option =
  { value: option.value
  , label: option.value
  , description: option.description
  , isSelected: isSelected selectedValue option.value
  }

-- | Dropdown class name
dropdownClassName :: String
dropdownClassName = "role-dropdown"
