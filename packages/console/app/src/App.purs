-- | Console Application Root
-- |
-- | Root application component providing:
-- | - Page metadata (title, description, OG tags)
-- | - Route management
-- | - Global layout (Favicon, Font)
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/app.tsx
-- | Migrated: 2026-02-03
module Console.App.App
  ( -- Types
    AppState
  , AppAction(..)
  , AppProps
  , Route(..)
    -- Component
  , component
  , defaultInput
    -- State management
  , initialState
  , reduce
    -- Metadata
  , defaultMetadata
  , PageMetadata
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Effect.Aff.Class (class MonadAff)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Properties as HP

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Page metadata for SEO
type PageMetadata =
  { title :: String
  , description :: String
  , ogImage :: Maybe String
  , canonicalPath :: Maybe String
  }

-- | Default page metadata
defaultMetadata :: PageMetadata
defaultMetadata =
  { title: "opencode"
  , description: "OpenCode - The open source coding agent."
  , ogImage: Nothing
  , canonicalPath: Nothing
  }

-- | Application routes
-- | Maps to SolidJS FileRoutes structure
data Route
  = Home                          -- /
  | Zen                           -- /zen
  | ZenV1ChatCompletions          -- /zen/v1/chat/completions
  | ZenV1Messages                 -- /zen/v1/messages
  | ZenV1Models                   -- /zen/v1/models
  | ZenV1ModelDetail String       -- /zen/v1/models/[model]
  | ZenV1Responses                -- /zen/v1/responses
  | Black                         -- /black
  | BlackSubscribe String         -- /black/subscribe/[plan]
  | BlackWorkspace                -- /black/workspace
  | Workspace                     -- /workspace
  | WorkspaceId String            -- /workspace/[id]
  | WorkspaceIdBilling String     -- /workspace/[id]/billing
  | WorkspaceIdKeys String        -- /workspace/[id]/keys
  | WorkspaceIdMembers String     -- /workspace/[id]/members
  | WorkspaceIdSettings String    -- /workspace/[id]/settings
  | Docs                          -- /docs
  | DocsPath String               -- /docs/[...path]
  | Download                      -- /download
  | Changelog                     -- /changelog
  | Brand                         -- /brand
  | Enterprise                    -- /enterprise
  | Bench                         -- /bench
  | BenchDetail String            -- /bench/[id]
  | Auth                          -- /auth
  | AuthCallback                  -- /auth/callback
  | AuthLogout                    -- /auth/logout
  | AuthStatus                    -- /auth/status
  | AuthAuthorize                 -- /auth/authorize
  | LegalPrivacy                  -- /legal/privacy-policy
  | LegalTerms                    -- /legal/terms-of-service
  | Debug                         -- /debug
  | NotFound                      -- /[...404]

derive instance eqRoute :: Eq Route

instance showRoute :: Show Route where
  show = case _ of
    Home -> "Home"
    Zen -> "Zen"
    ZenV1ChatCompletions -> "ZenV1ChatCompletions"
    ZenV1Messages -> "ZenV1Messages"
    ZenV1Models -> "ZenV1Models"
    ZenV1ModelDetail m -> "ZenV1ModelDetail(" <> m <> ")"
    ZenV1Responses -> "ZenV1Responses"
    Black -> "Black"
    BlackSubscribe p -> "BlackSubscribe(" <> p <> ")"
    BlackWorkspace -> "BlackWorkspace"
    Workspace -> "Workspace"
    WorkspaceId id -> "WorkspaceId(" <> id <> ")"
    WorkspaceIdBilling id -> "WorkspaceIdBilling(" <> id <> ")"
    WorkspaceIdKeys id -> "WorkspaceIdKeys(" <> id <> ")"
    WorkspaceIdMembers id -> "WorkspaceIdMembers(" <> id <> ")"
    WorkspaceIdSettings id -> "WorkspaceIdSettings(" <> id <> ")"
    Docs -> "Docs"
    DocsPath p -> "DocsPath(" <> p <> ")"
    Download -> "Download"
    Changelog -> "Changelog"
    Brand -> "Brand"
    Enterprise -> "Enterprise"
    Bench -> "Bench"
    BenchDetail id -> "BenchDetail(" <> id <> ")"
    Auth -> "Auth"
    AuthCallback -> "AuthCallback"
    AuthLogout -> "AuthLogout"
    AuthStatus -> "AuthStatus"
    AuthAuthorize -> "AuthAuthorize"
    LegalPrivacy -> "LegalPrivacy"
    LegalTerms -> "LegalTerms"
    Debug -> "Debug"
    NotFound -> "NotFound"

-- | App component input/props
type AppProps =
  { initialRoute :: Route
  }

-- | Default props
defaultInput :: AppProps
defaultInput =
  { initialRoute: Home
  }

-- | App component state
type AppState =
  { currentRoute :: Route
  , metadata :: PageMetadata
  , props :: AppProps
  }

-- | App component actions
data AppAction
  = Initialize
  | Navigate Route
  | UpdateMetadata PageMetadata

derive instance eqAppAction :: Eq AppAction

-- ═══════════════════════════════════════════════════════════════════════════════
-- STATE MANAGEMENT
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Initial state from props
initialState :: AppProps -> AppState
initialState props =
  { currentRoute: props.initialRoute
  , metadata: defaultMetadata
  , props
  }

-- | Pure reducer for app actions
reduce :: AppAction -> AppState -> AppState
reduce action state = case action of
  Initialize -> state
  Navigate route -> state { currentRoute = route }
  UpdateMetadata meta -> state { metadata = meta }

-- | Get metadata for a route
metadataForRoute :: Route -> PageMetadata
metadataForRoute = case _ of
  Home -> defaultMetadata
  Zen -> 
    { title: "OpenCode Zen | A curated set of reliable optimized models for coding agents"
    , description: "Zen gives you access to a curated set of AI models that OpenCode has tested and benchmarked specifically for coding agents."
    , ogImage: Just "/social-share-zen.png"
    , canonicalPath: Just "/zen"
    }
  Black ->
    { title: "OpenCode Black | Premium subscription"
    , description: "Get premium access to OpenCode with enhanced features."
    , ogImage: Nothing
    , canonicalPath: Just "/black"
    }
  Workspace ->
    { title: "Workspaces | OpenCode"
    , description: "Manage your OpenCode workspaces."
    , ogImage: Nothing
    , canonicalPath: Just "/workspace"
    }
  Docs ->
    { title: "Documentation | OpenCode"
    , description: "OpenCode documentation and guides."
    , ogImage: Nothing
    , canonicalPath: Just "/docs"
    }
  Download ->
    { title: "Download | OpenCode"
    , description: "Download OpenCode for your platform."
    , ogImage: Nothing
    , canonicalPath: Just "/download"
    }
  Enterprise ->
    { title: "Enterprise | OpenCode"
    , description: "OpenCode for enterprise teams."
    , ogImage: Nothing
    , canonicalPath: Just "/enterprise"
    }
  NotFound ->
    { title: "404 - Not Found | OpenCode"
    , description: "Page not found."
    , ogImage: Nothing
    , canonicalPath: Nothing
    }
  -- Default for all other routes
  _ -> defaultMetadata

-- ═══════════════════════════════════════════════════════════════════════════════
-- COMPONENT
-- ═══════════════════════════════════════════════════════════════════════════════

-- | App Halogen component
component :: forall q o m. MonadAff m => H.Component q AppProps o m
component = H.mkComponent
  { initialState
  , render
  , eval: H.mkEval $ H.defaultEval
      { handleAction = handleAction
      , initialize = Just Initialize
      }
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- RENDER
-- ═══════════════════════════════════════════════════════════════════════════════

render :: forall m. AppState -> H.ComponentHTML AppAction () m
render state =
  HH.div
    [ HP.class_ (HH.ClassName "app-root") ]
    [ renderMetadata state.metadata
    , renderRouteContent state.currentRoute
    ]

-- | Render metadata as hidden elements (in real app, uses document.head)
renderMetadata :: forall m. PageMetadata -> H.ComponentHTML AppAction () m
renderMetadata meta =
  HH.div
    [ HP.class_ (HH.ClassName "sr-only")
    , HP.attr (HH.AttrName "data-page-title") meta.title
    , HP.attr (HH.AttrName "data-page-description") meta.description
    ]
    []

-- | Render current route content
-- | In full implementation, this would render the appropriate page component
renderRouteContent :: forall m. Route -> H.ComponentHTML AppAction () m
renderRouteContent route =
  HH.div
    [ HP.class_ (HH.ClassName "route-content")
    , HP.attr (HH.AttrName "data-route") (show route)
    ]
    [ HH.text (show route)
    ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ACTIONS
-- ═══════════════════════════════════════════════════════════════════════════════

handleAction :: forall o m. MonadAff m => AppAction -> H.HalogenM AppState AppAction () o m Unit
handleAction = case _ of
  Initialize -> do
    -- Update metadata for initial route
    state <- H.get
    let meta = metadataForRoute state.currentRoute
    H.modify_ _ { metadata = meta }

  Navigate route -> do
    let meta = metadataForRoute route
    H.modify_ _ 
      { currentRoute = route
      , metadata = meta 
      }

  UpdateMetadata meta ->
    H.modify_ _ { metadata = meta }
