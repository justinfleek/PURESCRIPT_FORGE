-- | 404 Not Found Page
-- |
-- | Pure data representation for the 404 error page.
-- | Renders when no route matches.
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/routes/[...404].tsx
-- | Migrated: 2026-02-03
module Console.App.Routes.NotFound
  ( -- Types
    NotFoundPageMetadata
  , NotFoundAction
  , NotFoundLink
    -- Data
  , pageMetadata
  , navigationLinks
    -- Assets
  , logoLightPath
  , logoDarkPath
  ) where

import Prelude

import Console.App.Config as Config

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Page metadata for the 404 page
type NotFoundPageMetadata =
  { title :: String
  , statusCode :: Int
  }

-- | Navigation action/link on the 404 page
type NotFoundAction =
  { label :: String
  , url :: String
  , isExternal :: Boolean
  }

-- | Alias for navigation links
type NotFoundLink = NotFoundAction

-- ═══════════════════════════════════════════════════════════════════════════════
-- DATA
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Page metadata
pageMetadata :: NotFoundPageMetadata
pageMetadata =
  { title: "Not Found | opencode"
  , statusCode: 404
  }

-- | Navigation links shown on the 404 page
navigationLinks :: Array NotFoundLink
navigationLinks =
  [ { label: "Home"
    , url: "/"
    , isExternal: false
    }
  , { label: "Docs"
    , url: "/docs"
    , isExternal: false
    }
  , { label: "GitHub"
    , url: Config.github.repoUrl
    , isExternal: true
    }
  , { label: "Discord"
    , url: "/discord"
    , isExternal: false
    }
  ]

-- ═══════════════════════════════════════════════════════════════════════════════
-- ASSETS
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Path to the light theme logo
logoLightPath :: String
logoLightPath = "/asset/logo-ornate-light.svg"

-- | Path to the dark theme logo
logoDarkPath :: String
logoDarkPath = "/asset/logo-ornate-dark.svg"

-- | Page heading text
headingText :: String
headingText = "404 - Page Not Found"

-- | Alt text for logo images
logoAltLight :: String
logoAltLight = "opencode logo light"

logoAltDark :: String
logoAltDark = "opencode logo dark"
