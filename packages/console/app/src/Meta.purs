-- | Page Metadata Types
-- |
-- | Types and utilities for page metadata management.
-- | Corresponds to @solidjs/meta components (Title, Meta).
-- |
-- | Source: _OTHER/opencode-original/packages/console/app/src/app.tsx (MetaProvider usage)
-- | Migrated: 2026-02-03
module Console.App.Meta
  ( -- Types
    PageMetadata
  , OpenGraphMetadata
  , TwitterMetadata
  , FullMetadata
    -- Constructors
  , defaultMetadata
  , defaultOpenGraph
  , defaultTwitter
  , fullMetadata
    -- Utilities
  , mergeMetadata
  , formatTitle
  , buildCanonicalUrl
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe)
import Control.Alt ((<|>))
import Console.App.Config (baseUrl)

-- ═══════════════════════════════════════════════════════════════════════════════
-- TYPES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Core page metadata
type PageMetadata =
  { title :: String
  , description :: String
  , canonicalPath :: Maybe String
  }

-- | OpenGraph metadata for social sharing
type OpenGraphMetadata =
  { title :: Maybe String      -- Falls back to page title
  , description :: Maybe String -- Falls back to page description
  , image :: Maybe String
  , imageAlt :: Maybe String
  , url :: Maybe String        -- Falls back to canonical
  , siteName :: String
  , type_ :: String            -- "website", "article", etc.
  }

-- | Twitter card metadata
type TwitterMetadata =
  { card :: String             -- "summary", "summary_large_image", etc.
  , site :: Maybe String       -- @handle
  , creator :: Maybe String    -- @handle
  , title :: Maybe String      -- Falls back to OG/page title
  , description :: Maybe String -- Falls back to OG/page description
  , image :: Maybe String      -- Falls back to OG image
  }

-- | Complete metadata for a page
type FullMetadata =
  { page :: PageMetadata
  , og :: OpenGraphMetadata
  , twitter :: TwitterMetadata
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- CONSTRUCTORS
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Default page metadata
defaultMetadata :: PageMetadata
defaultMetadata =
  { title: "opencode"
  , description: "OpenCode - The open source coding agent."
  , canonicalPath: Nothing
  }

-- | Default OpenGraph metadata
defaultOpenGraph :: OpenGraphMetadata
defaultOpenGraph =
  { title: Nothing
  , description: Nothing
  , image: Nothing
  , imageAlt: Nothing
  , url: Nothing
  , siteName: "OpenCode"
  , type_: "website"
  }

-- | Default Twitter metadata
defaultTwitter :: TwitterMetadata
defaultTwitter =
  { card: "summary_large_image"
  , site: Just "@opencode"
  , creator: Nothing
  , title: Nothing
  , description: Nothing
  , image: Nothing
  }

-- | Build full metadata with fallbacks
fullMetadata :: PageMetadata -> Maybe OpenGraphMetadata -> Maybe TwitterMetadata -> FullMetadata
fullMetadata page mOg mTwitter =
  let
    og = fromMaybe defaultOpenGraph mOg
    twitter = fromMaybe defaultTwitter mTwitter
  in
    { page
    , og: og
        { title = og.title <|> Just page.title
        , description = og.description <|> Just page.description
        , url = og.url <|> (buildCanonicalUrl <$> page.canonicalPath)
        }
    , twitter: twitter
        { title = twitter.title <|> og.title <|> Just page.title
        , description = twitter.description <|> og.description <|> Just page.description
        , image = twitter.image <|> og.image
        }
    }

-- ═══════════════════════════════════════════════════════════════════════════════
-- UTILITIES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Merge two metadata records, preferring the second
mergeMetadata :: PageMetadata -> PageMetadata -> PageMetadata
mergeMetadata base override =
  { title: override.title
  , description: override.description
  , canonicalPath: override.canonicalPath <|> base.canonicalPath
  }

-- ═══════════════════════════════════════════════════════════════════════════════
-- UTILITIES
-- ═══════════════════════════════════════════════════════════════════════════════

-- | Merge two metadata records, preferring the second
mergeMetadata :: PageMetadata -> PageMetadata -> PageMetadata
mergeMetadata base override =
  { title: override.title
  , description: override.description
  , canonicalPath: override.canonicalPath <|> base.canonicalPath
  }
  where
    (<|>) :: forall a. Maybe a -> Maybe a -> Maybe a
    (<|>) (Just a) _ = Just a
    (<|>) Nothing b = b

-- | Format title with site suffix
formatTitle :: String -> String
formatTitle "" = "opencode"
formatTitle title = 
  if title == "opencode" 
    then title 
    else title <> " | opencode"

-- | Build full canonical URL from path
buildCanonicalUrl :: String -> String
buildCanonicalUrl path = baseUrl <> path
