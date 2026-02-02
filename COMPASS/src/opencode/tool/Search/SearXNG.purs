{-|
Module      : Tool.Search.SearXNG
Description : SearXNG HTTP client and execution
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= SearXNG Client

This module provides the HTTP client for communicating with SearXNG instances.
It handles request construction, response parsing, and error handling.

== Coeffect Equation

@
  performSearch : SearXNGConfig -> Query -> Graded Network (Either Error SearchResult)

  -- Requires:
  -- 1. Network access to SearXNG instance
  -- 2. JSON parsing capabilities
@

== SearXNG Architecture

@
  +-------------------------------------------------------------+
  |                         SearXNG Instance                    |
  +-------------------------------------------------------------+
  |                                                             |
  |  +----------+  +----------+  +----------+  +----------+     |
  |  |  Google  |  |  Bing    |  | DuckDuck |  |  Brave   | ... |
  |  +----+-----+  +----+-----+  +----+-----+  +----+-----+     |
  |       |             |             |             |           |
  |       +-------------+-------------+-------------+           |
  |                     |             |                         |
  |              +------+-------------+------+                  |
  |              |  Result Aggregation       |                  |
  |              |  Deduplication            |                  |
  |              |  Scoring                  |                  |
  |              +-----------+---------------+                  |
  |                          |                                  |
  +--------------------------|----------------------------------+
                             v
                      JSON API Response
@
-}
module Tool.Search.SearXNG
  ( -- * Configuration
    defaultConfig
    -- * HTTP Client
  , performSearch
  , parseResponse
    -- * Coeffects
  , searchCoeffect
  , mkSearchProof
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect (Effect)

import Tool.Search.Types
  ( SearXNGConfig
  , SearchResult
  , ApiFormat(..)
  , SafeSearchLevel(..)
  )
import Tool.Search.Query (Query, buildUrl)
import Aleph.Coeffect (Resource(..), NetworkAccess)

-- ============================================================================
-- CONFIGURATION
-- ============================================================================

-- | Default configuration (uses public instance)
defaultConfig :: SearXNGConfig
defaultConfig =
  { baseUrl: "https://searx.be"  -- Public instance; should be self-hosted
  , apiFormat: JsonFormat
  , timeout: 10000
  , enabledEngines: []           -- Empty = use instance defaults
  , disabledEngines: []
  , preferences:
      { language: "en"
      , safesearch: SafeSearchModerate
      , theme: "simple"
      , resultsOnNewTab: false
      , autocomplete: "duckduckgo"
      }
  }

-- ============================================================================
-- HTTP CLIENT
-- ============================================================================

{-| Perform search request to SearXNG.

This function:
1. Builds the API URL from config and query
2. Makes GET request with configured timeout
3. Parses JSON response
4. Transforms to SearchResult

@
  performSearch : SearXNGConfig -> Query -> Aff (Either String SearchResult)
@
-}
performSearch :: SearXNGConfig -> Query -> Aff (Either String SearchResult)
performSearch config query = do
  -- Build URL
  let url = buildUrl config query
  
  -- TODO: HTTP FFI implementation
  -- 1. Create HTTP request with timeout
  -- 2. Add appropriate headers (Accept: application/json)
  -- 3. Execute request
  -- 4. Parse JSON response
  -- 5. Transform to SearchResult
  notImplemented "performSearch"

{-| Parse SearXNG JSON response.

Transforms the raw JSON response into our SearchResult type.
Handles missing fields gracefully with defaults.
-}
parseResponse :: String -> Either String SearchResult
parseResponse _json = notImplemented "parseResponse"

-- ============================================================================
-- COEFFECTS
-- ============================================================================

{-| Coeffect for search operations.

Search requires network access to SearXNG instance.
-}
searchCoeffect :: Resource
searchCoeffect = Network

{-| Create network proof for search operation.

The proof captures:
- URL accessed
- Response hash for verification
- Timestamp of access
-}
mkSearchProof :: SearXNGConfig -> SearchResult -> NetworkAccess
mkSearchProof config _result =
  { url: config.baseUrl
  , responseHash: ""  -- TODO: Hash results
  , timestamp: 0.0    -- TODO: Get timestamp
  }

-- ============================================================================
-- HELPERS
-- ============================================================================

notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> Effect a
