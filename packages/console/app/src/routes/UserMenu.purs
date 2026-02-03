-- | User Menu Route
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/user-menu.tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.UserMenu
  ( UserMenuState(..)
  , UserMenuProps(..)
  , logoutUrl
  ) where

import Prelude

import Data.Maybe (Maybe)

-- | User menu props
type UserMenuProps =
  { email :: Maybe String
  }

-- | User menu state
type UserMenuState =
  { isOpen :: Boolean
  }

-- | Initial state
initialState :: UserMenuState
initialState = { isOpen: false }

-- | Logout URL
logoutUrl :: String
logoutUrl = "/auth/logout"

-- | Menu item
type MenuItem =
  { label :: String
  , href :: String
  }

-- | Menu items
menuItems :: Array MenuItem
menuItems =
  [ { label: "Logout", href: logoutUrl }
  ]
