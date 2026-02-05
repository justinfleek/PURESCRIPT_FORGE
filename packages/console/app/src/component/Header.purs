-- | Header Component
-- |
-- | Site header with navigation and branding.
-- | Pure data representation of header state and actions.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/component/header.tsx
module Forge.Console.App.Component.Header
  ( HeaderProps
  , HeaderState
  , HeaderAction(..)
  , NavItem(..)
  , initialState
  , reduce
  , getNavItems
  , formatStarCount
  ) where

import Prelude

import Data.Array as Array
import Data.Int (toNumber)
import Data.Maybe (Maybe(..))

-- | Header component props
type HeaderProps =
  { omega :: Boolean
  , hideGetStarted :: Boolean
  }

-- | Header component state
type HeaderState =
  { mobileMenuOpen :: Boolean
  , contextMenuOpen :: Boolean
  , contextMenuPosition :: { x :: Number, y :: Number }
  }

-- | Header actions
data HeaderAction
  = ToggleMobileMenu
  | OpenContextMenu { x :: Number, y :: Number }
  | CloseContextMenu
  | CopyLogo
  | CopyWordmark
  | NavigateToBrand

derive instance eqHeaderAction :: Eq HeaderAction

-- | Navigation item
data NavItem
  = GitHubLink { starCount :: String }
  | DocsLink
  | EnterpriseLink
  | OmegaLink
  | LoginLink
  | DownloadLink

derive instance eqNavItem :: Eq NavItem

-- | Initial header state
initialState :: HeaderState
initialState =
  { mobileMenuOpen: false
  , contextMenuOpen: false
  , contextMenuPosition: { x: 0.0, y: 0.0 }
  }

-- | Reduce header actions
reduce :: HeaderAction -> HeaderState -> HeaderState
reduce action state = case action of
  ToggleMobileMenu -> 
    state { mobileMenuOpen = not state.mobileMenuOpen }
  OpenContextMenu pos -> 
    state { contextMenuOpen = true, contextMenuPosition = pos }
  CloseContextMenu -> 
    state { contextMenuOpen = false }
  CopyLogo -> state
  CopyWordmark -> state
  NavigateToBrand -> state

-- | Get navigation items based on props
getNavItems :: HeaderProps -> Int -> Array NavItem
getNavItems props stars =
  let 
    baseItems = 
      [ GitHubLink { starCount: formatStarCount stars }
      , DocsLink
      , EnterpriseLink
      ]
    authItem = if props.omega then LoginLink else OmegaLink
    ctaItem = if props.hideGetStarted then [] else [DownloadLink]
  in baseItems <> [authItem] <> ctaItem

-- | Format star count with compact notation
formatStarCount :: Int -> String
formatStarCount stars
  | stars >= 1000000 = show (stars / 1000000) <> "M"
  | stars >= 1000 = show (stars / 1000) <> "K"
  | otherwise = show stars
