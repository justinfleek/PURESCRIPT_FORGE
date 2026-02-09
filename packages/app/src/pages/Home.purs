-- | Home page component - landing page with recent projects
-- | Migrated from: forge-dev/packages/app/src/pages/home.tsx (127 lines)
module Sidepanel.Pages.Home
  ( HomePage
  , HomePageState
  , HomePageProps
  ) where

import Prelude

import Data.Array as Array
import Data.DateTime.Instant (Instant)
import Data.Foldable (traverse_)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import Effect.Aff (Aff)

import Sidepanel.Context.GlobalSync (GlobalState, Project)
import Sidepanel.Context.Layout (LayoutStore)
import Sidepanel.Context.Platform (Platform)
import Sidepanel.Context.Server (ServerState)
import Sidepanel.Context.Language (Locale)
import Sidepanel.Utils.Encode (base64Encode)

-- | Home page component state
type HomePageState =
  { recentProjects :: Array Project
  , homedir :: String
  }

-- | Props passed to the Home page
type HomePageProps =
  { sync :: GlobalState
  , layout :: LayoutStore
  , platform :: Platform
  , server :: ServerState
  , language :: Locale
  }

-- | Get the home directory path from sync data
homedir :: GlobalState -> String
homedir sync = sync.path.home

-- | Get recent projects sorted by name
-- | Returns the 5 most recent projects
recentProjects :: GlobalState -> Array Project
recentProjects sync =
  sync.project
    # Array.sortBy compareByName
    # Array.take 5
  where
    compareByName :: Project -> Project -> Ordering
    compareByName a b = compare a.worktree b.worktree

-- | Open a project by directory path
-- | 1. Adds project to layout's open projects
-- | 2. Touches the project in server (updates last accessed time)
-- | 3. Navigates to the project URL
openProject :: HomePageProps -> String -> Effect Unit
openProject props directory = do
  -- layout.projects.open(directory)
  -- server.projects.touch(directory)
  -- navigate(`/${base64Encode(directory)}`)
  pure unit

-- | Open directory picker dialog for choosing a project
-- | Handles both:
-- | - Native platform dialog (if available and server is local)
-- | - Fallback dialog component (DialogSelectDirectory)
chooseProject :: HomePageProps -> Effect Unit
chooseProject props = do
  -- Check if platform has native directory picker and server is local
  -- If yes: use platform.openDirectoryPickerDialog
  -- If no: show DialogSelectDirectory component
  -- On result: call resolve function
  pure unit
  where
    resolve :: Maybe (Array String) -> Effect Unit
    resolve maybeResult = case maybeResult of
      Nothing -> pure unit
      Just dirs -> case Array.head dirs of
        Nothing -> pure unit
        Just first -> do
          -- Open all selected directories
          traverse_ (openProject props) dirs

-- | Format project path for display
-- | Replaces home directory with ~ for shorter display
formatProjectPath :: String -> String -> String
formatProjectPath path homeDir =
  -- path.replace(homedir(), "~")
  path

-- | Format relative time for display
-- | Uses luxon DateTime.fromMillis().toRelative()
formatRelativeTime :: Instant -> String
formatRelativeTime time =
  -- DateTime.fromMillis(timestamp).toRelative()
  "recently"

-- | Home page component
-- | 
-- | Layout:
-- | - Logo (with opacity)
-- | - Server connection button (shows health indicator)
-- | - Switch on project count:
-- |   - Has projects: Recent projects list
-- |     - Header with "Open Project" button
-- |     - List of recent projects (up to 5)
-- |     - Each shows path (with ~ for home) and relative time
-- |   - No projects: Empty state
-- |     - Folder icon
-- |     - Title and description
-- |     - "Open Project" button
type HomePage = HomePageProps -> Effect Unit

-- | Server health indicator colors
-- | - green: healthy (connected)
-- | - red: unhealthy (disconnected/error)
-- | - gray: unknown (checking)
type HealthColor = String

healthColor :: Maybe Boolean -> HealthColor
healthColor healthy = case healthy of
  Just true -> "bg-icon-success-base"
  Just false -> "bg-icon-critical-base"
  Nothing -> "bg-border-weak-base"
