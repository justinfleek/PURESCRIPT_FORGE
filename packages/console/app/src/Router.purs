-- | Application Router
-- |
-- | Route parsing, matching, and URL generation.
-- | Pure implementation - no FFI required.
-- |
-- | Corresponds to: @solidjs/router (Router, FileRoutes)
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/app.tsx
-- | Migrated: 2026-02-03
module Console.App.Router
  ( -- Types
    Route(..)
  , RouteMatch
  , RouteParams
    -- Parsing
  , parseRoute
  , matchRoute
    -- URL generation
  , routeToPath
  , routeToUrl
    -- Route utilities
  , isAuthRoute
  , isWorkspaceRoute
  , isOmegaRoute
  , isApiRoute
  , parentRoute
  ) where

import Prelude

import Data.Array as Array
import Data.Maybe (Maybe(..))
import Data.String as String
import Data.String.Pattern (Pattern(..))
import Console.App.Config (baseUrl)

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Application routes
-- | Comprehensive enumeration of all routes in the console app
data Route
  -- Root
  = Home                          -- /
  | NotFound                      -- /[...404]
  
  -- Omega (API proxy)
  | Omega                           -- /omega
  | OmegaV1ChatCompletions          -- /omega/v1/chat/completions
  | OmegaV1Messages                 -- /omega/v1/messages
  | OmegaV1Models                   -- /omega/v1/models
  | OmegaV1ModelDetail String       -- /omega/v1/models/[model]
  | OmegaV1Responses                -- /omega/v1/responses
  
  -- Black (subscription)
  | Black                         -- /black
  | BlackSubscribe String         -- /black/subscribe/[plan]
  | BlackWorkspace                -- /black/workspace
  
  -- Workspace
  | Workspace                     -- /workspace
  | WorkspaceId String            -- /workspace/[id]
  | WorkspaceIdBilling String     -- /workspace/[id]/billing
  | WorkspaceIdKeys String        -- /workspace/[id]/keys
  | WorkspaceIdMembers String     -- /workspace/[id]/members
  | WorkspaceIdSettings String    -- /workspace/[id]/settings
  
  -- Docs
  | Docs                          -- /docs
  | DocsPath String               -- /docs/[...path]
  
  -- Static pages
  | Download                      -- /download
  | Changelog                     -- /changelog
  | Brand                         -- /brand
  | Enterprise                    -- /enterprise
  
  -- Bench
  | Bench                         -- /bench
  | BenchDetail String            -- /bench/[id]
  
  -- Auth
  | Auth                          -- /auth
  | AuthCallback                  -- /auth/callback
  | AuthLogout                    -- /auth/logout
  | AuthStatus                    -- /auth/status
  | AuthAuthorize                 -- /auth/authorize
  
  -- Legal
  | LegalPrivacy                  -- /legal/privacy-policy
  | LegalTerms                    -- /legal/terms-of-service
  
  -- Debug
  | Debug                         -- /debug

derive instance eqRoute :: Eq Route

instance showRoute :: Show Route where
  show = routeToPath

-- | Route match result
type RouteMatch =
  { route :: Route
  , params :: RouteParams
  , path :: String
  }

-- | Dynamic route parameters
type RouteParams =
  { id :: Maybe String
  , path :: Maybe String
  , model :: Maybe String
  , plan :: Maybe String
  }

-- | Empty params
emptyParams :: RouteParams
emptyParams =
  { id: Nothing
  , path: Nothing
  , model: Nothing
  , plan: Nothing
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- PARSING
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Parse a URL path into a Route
parseRoute :: String -> Route
parseRoute path =
  let
    -- Remove leading/trailing slashes and split
    cleaned = path
      # String.trim
      # stripPrefix "/"
      # stripSuffix "/"
    segments = String.split (Pattern "/") cleaned
  in
    matchSegments (Array.filter (not <<< String.null) segments)

-- | Match path segments to a route
matchSegments :: Array String -> Route
matchSegments segments = case segments of
  -- Root
  [] -> Home
  
  -- Omega routes
  ["omega"] -> Omega
  ["omega", "v1", "chat", "completions"] -> OmegaV1ChatCompletions
  ["omega", "v1", "messages"] -> OmegaV1Messages
  ["omega", "v1", "models"] -> OmegaV1Models
  ["omega", "v1", "models", model] -> OmegaV1ModelDetail model
  ["omega", "v1", "responses"] -> OmegaV1Responses
  
  -- Black routes
  ["black"] -> Black
  ["black", "workspace"] -> BlackWorkspace
  ["black", "subscribe", plan] -> BlackSubscribe plan
  
  -- Workspace routes
  ["workspace"] -> Workspace
  ["workspace", id] -> WorkspaceId id
  ["workspace", id, "billing"] -> WorkspaceIdBilling id
  ["workspace", id, "keys"] -> WorkspaceIdKeys id
  ["workspace", id, "members"] -> WorkspaceIdMembers id
  ["workspace", id, "settings"] -> WorkspaceIdSettings id
  
  -- Docs routes
  ["docs"] -> Docs
  segs | Array.head segs == Just "docs" -> 
    DocsPath (String.joinWith "/" (Array.drop 1 segs))
  
  -- Static pages
  ["download"] -> Download
  ["changelog"] -> Changelog
  ["brand"] -> Brand
  ["enterprise"] -> Enterprise
  
  -- Bench routes
  ["bench"] -> Bench
  ["bench", id] -> BenchDetail id
  
  -- Auth routes
  ["auth"] -> Auth
  ["auth", "callback"] -> AuthCallback
  ["auth", "logout"] -> AuthLogout
  ["auth", "status"] -> AuthStatus
  ["auth", "authorize"] -> AuthAuthorize
  
  -- Legal routes
  ["legal", "privacy-policy"] -> LegalPrivacy
  ["legal", "terms-of-service"] -> LegalTerms
  
  -- Debug
  ["debug"] -> Debug
  
  -- Catch all
  _ -> NotFound

-- | Match route and extract parameters
matchRoute :: String -> RouteMatch
matchRoute path =
  let
    route = parseRoute path
    params = extractParams route path
  in
    { route, params, path }

-- | Extract parameters from a matched route
extractParams :: Route -> String -> RouteParams
extractParams route _ = case route of
  WorkspaceId id -> emptyParams { id = Just id }
  WorkspaceIdBilling id -> emptyParams { id = Just id }
  WorkspaceIdKeys id -> emptyParams { id = Just id }
  WorkspaceIdMembers id -> emptyParams { id = Just id }
  WorkspaceIdSettings id -> emptyParams { id = Just id }
  BenchDetail id -> emptyParams { id = Just id }
  DocsPath p -> emptyParams { path = Just p }
  OmegaV1ModelDetail m -> emptyParams { model = Just m }
  BlackSubscribe p -> emptyParams { plan = Just p }
  _ -> emptyParams

-- ═══════════════════════════════════════════════════════════════════════════════
-- URL GENERATION
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Convert a route to its URL path
routeToPath :: Route -> String
routeToPath = case _ of
  Home -> "/"
  NotFound -> "/404"
  
  Omega -> "/omega"
  OmegaV1ChatCompletions -> "/omega/v1/chat/completions"
  OmegaV1Messages -> "/omega/v1/messages"
  OmegaV1Models -> "/omega/v1/models"
  OmegaV1ModelDetail model -> "/omega/v1/models/" <> model
  OmegaV1Responses -> "/omega/v1/responses"
  
  Black -> "/black"
  BlackSubscribe plan -> "/black/subscribe/" <> plan
  BlackWorkspace -> "/black/workspace"
  
  Workspace -> "/workspace"
  WorkspaceId id -> "/workspace/" <> id
  WorkspaceIdBilling id -> "/workspace/" <> id <> "/billing"
  WorkspaceIdKeys id -> "/workspace/" <> id <> "/keys"
  WorkspaceIdMembers id -> "/workspace/" <> id <> "/members"
  WorkspaceIdSettings id -> "/workspace/" <> id <> "/settings"
  
  Docs -> "/docs"
  DocsPath p -> "/docs/" <> p
  
  Download -> "/download"
  Changelog -> "/changelog"
  Brand -> "/brand"
  Enterprise -> "/enterprise"
  
  Bench -> "/bench"
  BenchDetail id -> "/bench/" <> id
  
  Auth -> "/auth"
  AuthCallback -> "/auth/callback"
  AuthLogout -> "/auth/logout"
  AuthStatus -> "/auth/status"
  AuthAuthorize -> "/auth/authorize"
  
  LegalPrivacy -> "/legal/privacy-policy"
  LegalTerms -> "/legal/terms-of-service"
  
  Debug -> "/debug"

-- | Convert a route to a full URL
routeToUrl :: Route -> String
routeToUrl route = baseUrl <> routeToPath route

-- ═══════════════════════════════════════════════════════════════════════════════
-- ROUTE UTILITIES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Check if route is an auth route
isAuthRoute :: Route -> Boolean
isAuthRoute = case _ of
  Auth -> true
  AuthCallback -> true
  AuthLogout -> true
  AuthStatus -> true
  AuthAuthorize -> true
  _ -> false

-- | Check if route is a workspace route
isWorkspaceRoute :: Route -> Boolean
isWorkspaceRoute = case _ of
  Workspace -> true
  WorkspaceId _ -> true
  WorkspaceIdBilling _ -> true
  WorkspaceIdKeys _ -> true
  WorkspaceIdMembers _ -> true
  WorkspaceIdSettings _ -> true
  _ -> false

-- | Check if route is an omega route
isOmegaRoute :: Route -> Boolean
isOmegaRoute = case _ of
  Omega -> true
  OmegaV1ChatCompletions -> true
  OmegaV1Messages -> true
  OmegaV1Models -> true
  OmegaV1ModelDetail _ -> true
  OmegaV1Responses -> true
  _ -> false

-- | Check if route is an API route (not a page)
isApiRoute :: Route -> Boolean
isApiRoute = case _ of
  OmegaV1ChatCompletions -> true
  OmegaV1Messages -> true
  OmegaV1Models -> true
  OmegaV1ModelDetail _ -> true
  OmegaV1Responses -> true
  _ -> false

-- | Get parent route for navigation
parentRoute :: Route -> Maybe Route
parentRoute = case _ of
  Home -> Nothing
  NotFound -> Just Home
  
  Omega -> Just Home
  OmegaV1ChatCompletions -> Just Omega
  OmegaV1Messages -> Just Omega
  OmegaV1Models -> Just Omega
  OmegaV1ModelDetail _ -> Just OmegaV1Models
  OmegaV1Responses -> Just Omega
  
  Black -> Just Home
  BlackSubscribe _ -> Just Black
  BlackWorkspace -> Just Black
  
  Workspace -> Just Home
  WorkspaceId _ -> Just Workspace
  WorkspaceIdBilling id -> Just (WorkspaceId id)
  WorkspaceIdKeys id -> Just (WorkspaceId id)
  WorkspaceIdMembers id -> Just (WorkspaceId id)
  WorkspaceIdSettings id -> Just (WorkspaceId id)
  
  Docs -> Just Home
  DocsPath _ -> Just Docs
  
  Download -> Just Home
  Changelog -> Just Home
  Brand -> Just Home
  Enterprise -> Just Home
  
  Bench -> Just Home
  BenchDetail _ -> Just Bench
  
  Auth -> Just Home
  AuthCallback -> Just Auth
  AuthLogout -> Just Auth
  AuthStatus -> Just Auth
  AuthAuthorize -> Just Auth
  
  LegalPrivacy -> Just Home
  LegalTerms -> Just Home
  
  Debug -> Just Home

-- ═══════════════════════════════════════════════════════════════════════════════
-- HELPERS
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Strip prefix from string
stripPrefix :: String -> String -> String
stripPrefix prefix str =
  case String.stripPrefix (Pattern prefix) str of
    Just s -> s
    Nothing -> str

-- | Strip suffix from string
stripSuffix :: String -> String -> String
stripSuffix suffix str =
  case String.stripSuffix (Pattern suffix) str of
    Just s -> s
    Nothing -> str
