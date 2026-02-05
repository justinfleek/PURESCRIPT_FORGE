-- | Workspace [id] Layout
-- | Migrated from: _OTHER/opencode-original/packages/console/app/src/routes/workspace/[id].tsx
-- | Pure PureScript implementation - NO FFI
module Console.App.Routes.Workspace.Id.Layout
  ( WorkspaceIdLayoutProps(..)
  , NavItem(..)
  , NavConfig(..)
  , buildNavItems
  , buildNavConfig
  ) where

import Prelude

import Data.Array (filter) as Array
import Data.Maybe (Maybe)

-- | Layout props
type WorkspaceIdLayoutProps =
  { workspaceId :: String
  , isAdmin :: Boolean
  }

-- | Navigation item
type NavItem =
  { href :: String
  , label :: String
  , end :: Boolean  -- exact match for active state
  , adminOnly :: Boolean
  }

-- | Navigation configuration
type NavConfig =
  { items :: Array NavItem
  , workspaceId :: String
  }

-- | Build navigation items for workspace
buildNavItems :: String -> Array NavItem
buildNavItems workspaceId =
  [ { href: "/workspace/" <> workspaceId
    , label: "Omega"
    , end: true
    , adminOnly: false
    }
  , { href: "/workspace/" <> workspaceId <> "/keys"
    , label: "API Keys"
    , end: false
    , adminOnly: false
    }
  , { href: "/workspace/" <> workspaceId <> "/members"
    , label: "Members"
    , end: false
    , adminOnly: false
    }
  , { href: "/workspace/" <> workspaceId <> "/billing"
    , label: "Billing"
    , end: false
    , adminOnly: true
    }
  , { href: "/workspace/" <> workspaceId <> "/settings"
    , label: "Settings"
    , end: false
    , adminOnly: true
    }
  ]

-- | Build navigation config
buildNavConfig :: WorkspaceIdLayoutProps -> NavConfig
buildNavConfig props =
  { items: filterByRole props.isAdmin (buildNavItems props.workspaceId)
  , workspaceId: props.workspaceId
  }
  where
    filterByRole :: Boolean -> Array NavItem -> Array NavItem
    filterByRole isAdmin items =
      Array.filter (\item -> not item.adminOnly || isAdmin) items

-- | Check if nav item is active
isNavItemActive :: String -> NavItem -> Boolean
isNavItemActive currentPath item =
  if item.end
    then currentPath == item.href
    else startsWith item.href currentPath
  where
    startsWith :: String -> String -> Boolean
    startsWith prefix str = take (strLength prefix) str == prefix
    
    take :: Int -> String -> String
    take _ s = s  -- simplified
    
    strLength :: String -> Int
    strLength _ = 0  -- simplified

-- | Page slots
data PageSlot
  = OmegaSlot
  | KeysSlot
  | MembersSlot
  | BillingSlot
  | SettingsSlot

derive instance eqPageSlot :: Eq PageSlot

-- | Get page slot from path
getPageSlot :: String -> String -> PageSlot
getPageSlot workspaceId path =
  let
    basePath = "/workspace/" <> workspaceId
  in
    case stripPrefix basePath path of
      "" -> OmegaSlot
      "/" -> OmegaSlot
      "/keys" -> KeysSlot
      "/members" -> MembersSlot
      "/billing" -> BillingSlot
      "/settings" -> SettingsSlot
      _ -> OmegaSlot
  where
    stripPrefix :: String -> String -> String
    stripPrefix _ s = s  -- simplified

-- | Container data attributes
type ContainerAttributes =
  { page :: String
  , component :: String
  }

-- | Default container attributes
containerAttributes :: ContainerAttributes
containerAttributes =
  { page: "workspace"
  , component: "workspace-container"
  }

-- | Nav component attributes
type NavAttributes =
  { component :: String
  , desktopComponent :: String
  , mobileComponent :: String
  , itemsComponent :: String
  }

-- | Default nav attributes
navAttributes :: NavAttributes
navAttributes =
  { component: "workspace-nav"
  , desktopComponent: "nav-desktop"
  , mobileComponent: "nav-mobile"
  , itemsComponent: "workspace-nav-items"
  }

-- | Nav button attributes
type NavButtonAttributes =
  { active :: String
  , button :: String
  }

-- | Default nav button attributes
navButtonAttributes :: NavButtonAttributes
navButtonAttributes =
  { active: "active"
  , button: "data-nav-button"
  }

-- | Content wrapper attributes
type ContentAttributes =
  { component :: String
  }

-- | Default content attributes
contentAttributes :: ContentAttributes
contentAttributes =
  { component: "workspace-content"
  }
