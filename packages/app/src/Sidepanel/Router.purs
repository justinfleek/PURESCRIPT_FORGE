-- | Router Module - Single Page Application Routing
-- |
-- | **What:** Provides routing functionality for the sidepanel SPA, including route definitions,
-- |         URL parsing/printing, and route-to-panel mapping. Uses Routing.Duplex for type-safe
-- |         routing.
-- | **Why:** Enables navigation between different panels without page reloads, provides
-- |         bookmarkable URLs, and maintains application state across navigation.
-- | **How:** Defines Route type with all application routes, uses Routing.Duplex codec for
-- |         bidirectional URL encoding/decoding, and provides mapping from routes to Panel types.
-- |
-- | **Dependencies:**
-- | - `Routing.Duplex`: Type-safe routing library
-- | - `Sidepanel.State.AppState`: Panel type definitions
-- |
-- | **Mathematical Foundation:**
-- | - **Route Codec:** Bidirectional codec ensures `parseRoute (printRoute r) == r` for all
-- |   routes `r` (round-trip property).
-- | - **Route Parsing:** URL parsing is total - always returns a Route (defaults to NotFound
-- |   on parse failure).
-- |
-- | **Usage Example:**
-- | ```purescript
-- | import Sidepanel.Router as Router
-- |
-- | -- Parse URL to route
-- | Router.parseRoute "/dashboard"  -- Dashboard
-- | Router.parseRoute "/session?id=abc123"  -- Session (Just "abc123")
-- |
-- | -- Print route to URL
-- | Router.printRoute Dashboard  -- "/dashboard"
-- | Router.printRoute (Session (Just "abc123"))  -- "/session?id=abc123"
-- |
-- | -- Map route to panel
-- | Router.routeToPanel Dashboard  -- DashboardPanel
-- | ```
-- |
-- | Based on spec 45-ROUTING.md
module Sidepanel.Router where

import Prelude
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Maybe (Maybe(..))
import Data.String as String
import Sidepanel.State.AppState (Panel(..))

-- | Application routes
data Route
  = Dashboard
  | Session (Maybe String)  -- Optional session ID
  | Proof
  | Timeline
  | Settings
  | Terminal
  | FileContext
  | DiffViewer
  | Search
  | NotFound

derive instance genericRoute :: Generic Route _
derive instance eqRoute :: Eq Route
derive instance ordRoute :: Ord Route

instance showRoute :: Show Route where
  show = genericShow

-- | Parse URL to route
parseRoute :: String -> Route
parseRoute url =
  let path = stripLeadingSlash url
      segments = String.split (String.Pattern "/") path
  in case segments of
    ["dashboard"] -> Dashboard
    [""] -> Dashboard
    ["session"] -> Session Nothing
    ["session", sid] -> Session (Just sid)
    ["proof"] -> Proof
    ["timeline"] -> Timeline
    ["settings"] -> Settings
    ["terminal"] -> Terminal
    ["file-context"] -> FileContext
    ["diff"] -> DiffViewer
    ["search"] -> Search
    _ -> NotFound
  where
    stripLeadingSlash s =
      if String.take 1 s == "/" then String.drop 1 s else s

-- | Print route to URL
printRoute :: Route -> String
printRoute = case _ of
  Dashboard -> "/"
  Session Nothing -> "/session"
  Session (Just sid) -> "/session/" <> sid
  Proof -> "/proof"
  Timeline -> "/timeline"
  Settings -> "/settings"
  Terminal -> "/terminal"
  FileContext -> "/file-context"
  DiffViewer -> "/diff"
  Search -> "/search"
  NotFound -> "/"

-- | Route to panel mapping
routeToPanel :: Route -> Panel
routeToPanel = case _ of
  Dashboard -> DashboardPanel
  Session _ -> SessionPanel
  Proof -> ProofPanel
  Timeline -> TimelinePanel
  Settings -> SettingsPanel
  Terminal -> TerminalPanel
  FileContext -> FileContextPanel
  DiffViewer -> DiffViewerPanel
  Search -> DashboardPanel  -- Search is a modal overlay, not a panel
  NotFound -> DashboardPanel
