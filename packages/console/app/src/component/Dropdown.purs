-- | Dropdown Component
-- |
-- | Dropdown menu with trigger button.
-- | Pure data representation of dropdown state and actions.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/component/dropdown.tsx
module Forge.Console.App.Component.Dropdown
  ( DropdownProps
  , DropdownState
  , DropdownAction(..)
  , DropdownAlign(..)
  , DropdownItem
  , initialState
  , reduce
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- | Dropdown alignment
data DropdownAlign
  = AlignLeft
  | AlignRight

derive instance eqDropdownAlign :: Eq DropdownAlign

instance showDropdownAlign :: Show DropdownAlign where
  show AlignLeft = "left"
  show AlignRight = "right"

-- | Dropdown component props
type DropdownProps =
  { trigger :: String
  , align :: DropdownAlign
  , open :: Maybe Boolean
  }

-- | Dropdown component state
type DropdownState =
  { isOpen :: Boolean
  }

-- | Dropdown item
type DropdownItem =
  { selected :: Boolean
  , label :: String
  }

-- | Dropdown actions
data DropdownAction
  = Toggle
  | Open
  | Close
  | ClickOutside
  | SelectItem Int

derive instance eqDropdownAction :: Eq DropdownAction

-- | Initial dropdown state
initialState :: DropdownState
initialState = { isOpen: false }

-- | Reduce dropdown actions
reduce :: DropdownAction -> DropdownState -> DropdownState
reduce action state = case action of
  Toggle -> state { isOpen = not state.isOpen }
  Open -> state { isOpen = true }
  Close -> state { isOpen = false }
  ClickOutside -> state { isOpen = false }
  SelectItem _ -> state { isOpen = false }
