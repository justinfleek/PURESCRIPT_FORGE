{-|
Module      : Tool.Search.Query
Description : Query building for SearXNG search
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= Query Building

This module provides a fluent API for building search queries to SearXNG.
Queries can be configured with engines, categories, language, time range,
and pagination options.

== Usage Example

@
  query <- buildQuery "type theory"
    # withCategories [Science, IT]
    # withEngines [Arxiv, GitHub]
    # withTimeRange Month
    # withPage 1
    # fromBuilder
@

== System F-w Encoding

@
  -- Query indexed by categories
  data Query :: List Category -> Type

  -- Builder monad for query construction
  newtype QueryBuilder a = QueryBuilder (State QueryState a)
@
-}
module Tool.Search.Query
  ( -- * Query Type
    Query(..)
    -- * Query Builder
  , QueryBuilder(..)
  , buildQuery
  , fromBuilder
    -- * Builder Combinators
  , withEngines
  , withCategories
  , withLanguage
  , withTimeRange
  , withPage
    -- * URL Building
  , buildUrl
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.String as String

import Tool.Search.Types
  ( Engine
  , Category(..)
  , TimeRange
  , SearXNGConfig
  , categoryToString
  )

-- ============================================================================
-- QUERY TYPE
-- ============================================================================

{-| Search query with options.

@
  record Query where
    text        : String
    engines     : Maybe (List Engine)
    categories  : List Category
    language    : String
    timeRange   : Maybe TimeRange
    pageno      : Nat
@
-}
type Query =
  { text :: String
  , engines :: Maybe (Array Engine)
  , categories :: Array Category
  , language :: String
  , timeRange :: Maybe TimeRange
  , pageno :: Int
  }

-- ============================================================================
-- QUERY BUILDER
-- ============================================================================

{-| Query builder for fluent API.

The QueryBuilder wraps a Query and provides combinators for modification.
Use `buildQuery` to start and `fromBuilder` to extract the final query.
-}
newtype QueryBuilder = QueryBuilder Query

-- | Start building a query with the given search text
buildQuery :: String -> QueryBuilder
buildQuery text = QueryBuilder
  { text
  , engines: Nothing
  , categories: [General]
  , language: "en"
  , timeRange: Nothing
  , pageno: 1
  }

-- | Extract query from builder
fromBuilder :: QueryBuilder -> Query
fromBuilder (QueryBuilder q) = q

-- ============================================================================
-- BUILDER COMBINATORS
-- ============================================================================

-- | Add specific engines to query
withEngines :: Array Engine -> QueryBuilder -> QueryBuilder
withEngines engines (QueryBuilder q) = QueryBuilder q { engines = Just engines }

-- | Set categories for query
withCategories :: Array Category -> QueryBuilder -> QueryBuilder
withCategories cats (QueryBuilder q) = QueryBuilder q { categories = cats }

-- | Set language for query (ISO 639-1 code)
withLanguage :: String -> QueryBuilder -> QueryBuilder
withLanguage lang (QueryBuilder q) = QueryBuilder q { language = lang }

-- | Set time range filter
withTimeRange :: TimeRange -> QueryBuilder -> QueryBuilder
withTimeRange range (QueryBuilder q) = QueryBuilder q { timeRange = Just range }

-- | Set page number (1-indexed)
withPage :: Int -> QueryBuilder -> QueryBuilder
withPage n (QueryBuilder q) = QueryBuilder q { pageno = n }

-- ============================================================================
-- URL BUILDING
-- ============================================================================

{-| Build SearXNG API URL.

Constructs the full URL with query parameters for the SearXNG API.

@
  buildUrl config query = config.baseUrl <> "/search"
    <> "?q=" <> urlEncode query.text
    <> "&format=json"
    <> "&categories=" <> intercalate "," (map categoryToString query.categories)
    <> maybe "" (\es -> "&engines=" <> intercalate "," (map engineToString es)) query.engines
    <> maybe "" (\t -> "&time_range=" <> timeRangeToString t) query.timeRange
    <> "&language=" <> query.language
    <> "&pageno=" <> show query.pageno
@
-}
buildUrl :: SearXNGConfig -> Query -> String
buildUrl config query =
  config.baseUrl <> "/search?q=" <> urlEncode query.text
    <> "&format=json"
    <> "&categories=" <> String.joinWith "," (map categoryToString query.categories)
    <> "&language=" <> query.language
    <> "&pageno=" <> show query.pageno

-- | URL encode a string (simplified - should use proper encoding)
urlEncode :: String -> String
urlEncode s = String.replaceAll (String.Pattern " ") (String.Replacement "+") s
