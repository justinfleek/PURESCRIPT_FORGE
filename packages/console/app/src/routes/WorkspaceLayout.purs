-- | Workspace Layout Route
-- |
-- | Layout wrapper for workspace pages.
-- | Provides header with navigation, workspace picker, and user menu.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/workspace.tsx
-- | Migrated: 2026-02-03
module Console.App.Routes.WorkspaceLayout
  ( -- Types
    WorkspaceLayoutProps
  , WorkspaceLayoutState
  , WorkspaceLayoutAction(..)
    -- State management
  , initialState
  , reduce
    -- Query helpers
  , getUserEmailQuery
  ) where

import Prelude

import Data.Maybe (Maybe(..))

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Workspace layout props
type WorkspaceLayoutProps =
  { workspaceId :: String
  }

-- | Workspace layout state
type WorkspaceLayoutState =
  { workspaceId :: String
  , userEmail :: Maybe String
  , loading :: Boolean
  }

-- | Workspace layout actions
data WorkspaceLayoutAction
  = Initialize String              -- Initialize with workspace ID
  | SetUserEmail (Maybe String)    -- Set user email from query
  | SetLoading Boolean             -- Set loading state

derive instance eqWorkspaceLayoutAction :: Eq WorkspaceLayoutAction

instance showWorkspaceLayoutAction :: Show WorkspaceLayoutAction where
  show (Initialize id) = "(Initialize " <> id <> ")"
  show (SetUserEmail email) = "(SetUserEmail " <> show email <> ")"
  show (SetLoading b) = "(SetLoading " <> show b <> ")"

-- ═══════════════════════════════════════════════════════════════════════════════
-- STATE MANAGEMENT
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initial state
initialState :: WorkspaceLayoutProps -> WorkspaceLayoutState
initialState props =
  { workspaceId: props.workspaceId
  , userEmail: Nothing
  , loading: true
  }

-- | Pure reducer
reduce :: WorkspaceLayoutAction -> WorkspaceLayoutState -> WorkspaceLayoutState
reduce action state = case action of
  Initialize workspaceId ->
    state { workspaceId = workspaceId, loading = true }
  
  SetUserEmail email ->
    state { userEmail = email, loading = false }
  
  SetLoading loading ->
    state { loading = loading }

-- ═══════════════════════════════════════════════════════════════════════════════
-- QUERY HELPERS
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Query key for getting user email
-- | In the TypeScript version, this uses @solidjs/router's `query` function
-- | with server-side execution
getUserEmailQuery :: String
getUserEmailQuery = "userEmail"

-- | Build the query URL for user email
-- | The actual query will be implemented in the effect layer
buildUserEmailQueryUrl :: String -> String
buildUserEmailQueryUrl workspaceId = "/api/workspace/" <> workspaceId <> "/user/email"

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONTENT
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Home link URL
homeLinkUrl :: String
homeLinkUrl = "/"

-- | Header component slots
type HeaderSlots =
  { brand :: Boolean
  , actions :: Boolean
  }

defaultHeaderSlots :: HeaderSlots
defaultHeaderSlots =
  { brand: true
  , actions: true
  }
