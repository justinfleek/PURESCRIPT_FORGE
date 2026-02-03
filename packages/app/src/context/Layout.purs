-- | Layout context - manages UI layout state
-- | Migrated from: forge-dev/packages/app/src/context/layout.tsx
module App.Context.Layout
  ( AvatarColorKey(..)
  , LocalProject
  , ReviewDiffStyle(..)
  , SessionTabs
  , SessionView
  , LayoutStore
  , mkLayoutStore
  , getAvatarColors
  , avatarColorKeys
  ) where

import Prelude

import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))

-- | Avatar color keys
data AvatarColorKey
  = Pink
  | Mint
  | Orange
  | Purple
  | Cyan
  | Lime

derive instance eqAvatarColorKey :: Eq AvatarColorKey

instance showAvatarColorKey :: Show AvatarColorKey where
  show Pink = "pink"
  show Mint = "mint"
  show Orange = "orange"
  show Purple = "purple"
  show Cyan = "cyan"
  show Lime = "lime"

-- | All avatar color keys
avatarColorKeys :: Array AvatarColorKey
avatarColorKeys = [Pink, Mint, Orange, Purple, Cyan, Lime]

-- | Get avatar colors (CSS variables)
getAvatarColors :: Maybe AvatarColorKey -> { background :: String, foreground :: String }
getAvatarColors (Just key) =
  { background: "var(--avatar-background-" <> show key <> ")"
  , foreground: "var(--avatar-text-" <> show key <> ")"
  }
getAvatarColors Nothing =
  { background: "var(--surface-info-base)"
  , foreground: "var(--text-base)"
  }

-- | Session tabs state
type SessionTabs =
  { active :: Maybe String
  , all :: Array String
  }

-- | Session scroll position
type SessionScroll =
  { x :: Number
  , y :: Number
  }

-- | Session view state
type SessionView =
  { scroll :: Map String SessionScroll
  , reviewOpen :: Maybe (Array String)
  }

-- | Review diff style
data ReviewDiffStyle
  = Unified
  | Split

derive instance eqReviewDiffStyle :: Eq ReviewDiffStyle

instance showReviewDiffStyle :: Show ReviewDiffStyle where
  show Unified = "unified"
  show Split = "split"

-- | Local project info
type LocalProject =
  { worktree :: String
  , expanded :: Boolean
  , id :: Maybe String
  , name :: Maybe String
  }

-- | Sidebar state
type SidebarState =
  { opened :: Boolean
  , width :: Int
  , workspaces :: Map String Boolean
  , workspacesDefault :: Boolean
  }

-- | Terminal panel state
type TerminalState =
  { height :: Int
  , opened :: Boolean
  }

-- | Review state
type ReviewState =
  { diffStyle :: ReviewDiffStyle
  }

-- | File tree state
type FileTreeState =
  { opened :: Boolean
  , width :: Int
  , tab :: String  -- "changes" | "all"
  }

-- | Session panel state
type SessionState =
  { width :: Int
  }

-- | Mobile sidebar state
type MobileSidebarState =
  { opened :: Boolean
  }

-- | Layout store
type LayoutStore =
  { sidebar :: SidebarState
  , terminal :: TerminalState
  , review :: ReviewState
  , fileTree :: FileTreeState
  , session :: SessionState
  , mobileSidebar :: MobileSidebarState
  , sessionTabs :: Map String SessionTabs
  , sessionView :: Map String SessionView
  }

-- | Create initial layout store
mkLayoutStore :: LayoutStore
mkLayoutStore =
  { sidebar:
      { opened: false
      , width: 344
      , workspaces: Map.empty
      , workspacesDefault: false
      }
  , terminal:
      { height: 280
      , opened: false
      }
  , review:
      { diffStyle: Split
      }
  , fileTree:
      { opened: true
      , width: 344
      , tab: "changes"
      }
  , session:
      { width: 600
      }
  , mobileSidebar:
      { opened: false
      }
  , sessionTabs: Map.empty
  , sessionView: Map.empty
  }
