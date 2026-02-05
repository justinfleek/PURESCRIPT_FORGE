{-|
Module      : Tool.Search.Types
Description : Type definitions for SearXNG search
= Search Types

Core type definitions for the SearXNG metasearch integration.
Contains parameter types, result types, and configuration types.

== Module Dependencies

* "Tool.Search.Engines" - Engine and Category definitions
-}
module Tool.Search.Types
  ( -- * Re-exports from Engines
    module Tool.Search.Engines
    -- * Search Parameters
  , SearchParams(..)
  , SearchResult(..)
  , ResultItem(..)
  , Infobox(..)
    -- * Configuration
  , SearXNGConfig(..)
  , ApiFormat(..)
  , Preferences(..)
  , SafeSearchLevel(..)
    -- * Result Types
  , WebResult(..)
  , ImageResult(..)
  , VideoResult(..)
  , CodeResult(..)
  , ScientificResult(..)
    -- * Time Range
  , TimeRange(..)
  , timeRangeToString
  ) where

import Prelude

import Data.Maybe (Maybe)
import Data.Generic.Rep (class Generic)
import Data.Show.Generic (genericShow)
import Data.Argonaut (Json)

import Tool.Search.Engines

-- ============================================================================
-- SEARCH PARAMETERS
-- ============================================================================

{-| Search tool parameters.

@
  record SearchParams where
    query       : String
    categories  : List Category
    engines     : Maybe (List Engine)
    language    : String
    timeRange   : Maybe TimeRange
    safesearch  : SafeSearchLevel
    pageno      : Nat
    limit       : Nat
@
-}
type SearchParams =
  { query :: String
  , categories :: Array Category
  , engines :: Maybe (Array Engine)
  , language :: String
  , timeRange :: Maybe TimeRange
  , safesearch :: SafeSearchLevel
  , pageno :: Int
  , limit :: Int
  }

{-| Search result from SearXNG. -}
type SearchResult =
  { results :: Array ResultItem
  , infoboxes :: Array Infobox
  , suggestions :: Array String
  , corrections :: Array String
  , unresponsiveEngines :: Array String
  , searchTimeMs :: Int
  , totalResults :: Maybe Int
  }

type ResultItem =
  { title :: String
  , url :: String
  , content :: String
  , engine :: String
  , category :: Category
  , score :: Number
  , publishedDate :: Maybe String
  , thumbnail :: Maybe String
  , metadata :: Json
  }

type Infobox =
  { title :: String
  , content :: String
  , urls :: Array { title :: String, url :: String }
  , img_src :: Maybe String
  , engine :: String
  }

-- ============================================================================
-- CONFIGURATION
-- ============================================================================

{-| SearXNG instance configuration. -}
type SearXNGConfig =
  { baseUrl :: String
  , apiFormat :: ApiFormat
  , timeout :: Int
  , enabledEngines :: Array Engine
  , disabledEngines :: Array Engine
  , preferences :: Preferences
  }

data ApiFormat
  = JsonFormat
  | RssFormat
  | CsvFormat

derive instance eqApiFormat :: Eq ApiFormat
derive instance genericApiFormat :: Generic ApiFormat _

instance showApiFormat :: Show ApiFormat where
  show = genericShow

type Preferences =
  { language :: String
  , safesearch :: SafeSearchLevel
  , theme :: String
  , resultsOnNewTab :: Boolean
  , autocomplete :: String
  }

data SafeSearchLevel
  = SafeSearchOff
  | SafeSearchModerate
  | SafeSearchStrict

derive instance eqSafeSearchLevel :: Eq SafeSearchLevel
derive instance genericSafeSearchLevel :: Generic SafeSearchLevel _

instance showSafeSearchLevel :: Show SafeSearchLevel where
  show = genericShow

-- ============================================================================
-- TIME RANGE
-- ============================================================================

data TimeRange
  = Day
  | Week
  | Month
  | Year

derive instance eqTimeRange :: Eq TimeRange
derive instance genericTimeRange :: Generic TimeRange _

instance showTimeRange :: Show TimeRange where
  show = genericShow

timeRangeToString :: TimeRange -> String
timeRangeToString = case _ of
  Day -> "day"
  Week -> "week"
  Month -> "month"
  Year -> "year"

-- ============================================================================
-- RESULT TYPES
-- ============================================================================

{-| Web search result. -}
type WebResult =
  { title :: String
  , url :: String
  , snippet :: String
  , engine :: String
  , score :: Number
  , cachedUrl :: Maybe String
  , publishedDate :: Maybe String
  }

{-| Image search result. -}
type ImageResult =
  { title :: String
  , url :: String
  , thumbnailUrl :: String
  , sourceUrl :: String
  , width :: Int
  , height :: Int
  , format :: String
  , engine :: String
  }

{-| Video search result. -}
type VideoResult =
  { title :: String
  , url :: String
  , thumbnailUrl :: String
  , duration :: Maybe Int
  , author :: String
  , platform :: String
  , views :: Maybe Int
  , publishedDate :: Maybe String
  }

{-| Code search result. -}
type CodeResult =
  { title :: String
  , url :: String
  , repository :: String
  , filepath :: Maybe String
  , snippet :: String
  , language :: Maybe String
  , stars :: Maybe Int
  , lastUpdated :: Maybe String
  }

{-| Scientific/academic result. -}
type ScientificResult =
  { title :: String
  , url :: String
  , abstract :: String
  , authors :: Array String
  , venue :: String
  , year :: Int
  , citations :: Maybe Int
  , doi :: Maybe String
  , arxivId :: Maybe String
  , pdfUrl :: Maybe String
  }
