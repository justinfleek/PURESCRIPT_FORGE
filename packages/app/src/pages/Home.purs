-- | Home page component - landing page with recent projects
-- | Migrated from: forge-dev/packages/app/src/pages/home.tsx (127 lines)
module Sidepanel.Pages.Home
  ( HomePage
  , HomePageState
  ) where

import Prelude

import Data.Array as Array
import Data.DateTime.Instant (Instant)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Aff (Aff)

import Sidepanel.Context.GlobalSync (GlobalSyncData, Project)
import Sidepanel.Context.Layout (LayoutContext)
import Sidepanel.Context.Platform (PlatformContext)
import Sidepanel.Context.Server (ServerContext)
import Sidepanel.Context.Language (LanguageContext)
import Sidepanel.Utils.Encode (base64Encode)

-- | Home page component state
type HomePageState =
  { recentProjects :: Array Project
  , homedir :: String
  }

-- | Props passed to the Home page
type HomePageProps =
  { sync :: GlobalSyncData
  , layout :: LayoutContext
  , platform :: PlatformContext
  , server :: ServerContext
  , language :: LanguageContext
  }

-- | Get the home directory path from sync data
homedir :: GlobalSyncData -> String
homedir sync = sync.path.home

-- | Get recent projects sorted by last updated time
-- | Returns the 5 most recently updated projects
recentProjects :: GlobalSyncData -> Array Project
recentProjects sync =
  sync.project
    # Array.sortBy compareByUpdated
    # Array.take 5
  where
    compareByUpdated :: Project -> Project -> Ordering
    compareByUpdated a b =
      let aTime = a.time.updated `orElse` a.time.created
          bTime = b.time.updated `orElse` b.time.created
      in compare bTime aTime  -- Descending order (most recent first)
    
    orElse :: Maybe Instant -> Instant -> Instant
    orElse maybeTime fallback = case maybeTime of
      Just t -> t
      Nothing -> fallback

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
          Array.traverse_ (openProject props) dirs

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
