{-|
Module      : Tool.Search.SearXNG
Description : SearXNG HTTP client and execution
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
import Data.Argonaut (encodeJson)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect (Effect)

import Tool.Search.SearXNG.FFI (httpGetWithTimeout, nowMillis, hashString)
import Tool.Search.Types
  ( SearXNGConfig
  , SearchResult
  , ApiFormat(..)
  , SafeSearchLevel(..)
  , ResultItem(..)
  , Infobox(..)
  )
import Tool.Search.Query (Query, buildUrl)
import Aleph.Coeffect (Resource(..), NetworkAccess)
import Data.Argonaut (Json, jsonParser, decodeJson, (.:), (.:?))
import Data.Argonaut.Decode.Class (class DecodeJson)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Array as Array
import Data.Traversable (traverse)

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
  
  -- Make HTTP request with timeout
  httpResult <- httpGetWithTimeout config.timeout url
  case httpResult of
    Left err -> pure $ Left ("HTTP request failed: " <> err)
    Right response -> do
      -- Check status code
      if response.statusCode < 200 || response.statusCode >= 300 then
        pure $ Left ("HTTP error: status " <> show response.statusCode)
      else do
        -- Parse JSON response
        let parseResult = parseResponse response.body
        case parseResult of
          Left err -> pure $ Left ("Parse error: " <> err)
          Right searchResult -> pure $ Right searchResult

{-| Parse SearXNG JSON response.

Transforms the raw JSON response into our SearchResult type.
Handles missing fields gracefully with defaults.
-}
parseResponse :: String -> Either String SearchResult
parseResponse jsonStr = do
  json <- jsonParser jsonStr
  parseSearXNGResponse json

-- | Parse SearXNG JSON response object
parseSearXNGResponse :: Json -> Either String SearchResult
parseSearXNGResponse json = do
  obj <- decodeJson json
  results <- obj .: "results" >>= decodeJsonArray parseResultItem
  infoboxes <- (obj .:? "infoboxes") >>= \mb -> pure $ fromMaybe [] (mb >>= decodeJsonArray parseInfobox)
  suggestions <- (obj .:? "suggestions") >>= \mb -> pure $ fromMaybe [] (mb >>= decodeJsonArray decodeJson)
  corrections <- (obj .:? "corrections") >>= \mb -> pure $ fromMaybe [] (mb >>= decodeJsonArray decodeJson)
  unresponsiveEngines <- (obj .:? "unresponsive_engines") >>= \mb -> pure $ fromMaybe [] (mb >>= decodeJsonArray decodeJson)
  searchTimeMs <- (obj .:? "number_of_results") >>= \mb -> pure $ fromMaybe 0 (mb >>= decodeJson)
  totalResults <- obj .:? "number_of_results" >>= \mb -> pure (mb >>= decodeJson)
  
  pure
    { results: results
    , infoboxes: infoboxes
    , suggestions: suggestions
    , corrections: corrections
    , unresponsiveEngines: unresponsiveEngines
    , searchTimeMs: searchTimeMs
    , totalResults: totalResults
    }

-- | Parse a single result item
parseResultItem :: Json -> Either String ResultItem
parseResultItem json = do
  obj <- decodeJson json
  title <- obj .: "title" >>= decodeJson
  url <- obj .: "url" >>= decodeJson
  content <- (obj .:? "content") >>= \mb -> pure $ fromMaybe "" (mb >>= decodeJson)
  engine <- (obj .:? "engine") >>= \mb -> pure $ fromMaybe "unknown" (mb >>= decodeJson)
  category <- (obj .:? "category") >>= \mb -> pure $ fromMaybe General (mb >>= decodeJson)
  score <- (obj .:? "score") >>= \mb -> pure $ fromMaybe 0.0 (mb >>= decodeJson)
  publishedDate <- obj .:? "publishedDate" >>= \mb -> pure (mb >>= decodeJson)
  thumbnail <- obj .:? "thumbnail" >>= \mb -> pure (mb >>= decodeJson)
  metadata <- pure json
  
  pure
    { title: title
    , url: url
    , content: content
    , engine: engine
    , category: category
    , score: score
    , publishedDate: publishedDate
    , thumbnail: thumbnail
    , metadata: metadata
    }

-- | Parse an infobox
parseInfobox :: Json -> Either String Infobox
parseInfobox json = do
  obj <- decodeJson json
  title <- obj .: "infobox" >>= decodeJson
  content <- (obj .:? "content") >>= \mb -> pure $ fromMaybe "" (mb >>= decodeJson)
  urls <- (obj .:? "urls") >>= \mb -> pure $ fromMaybe [] (mb >>= decodeJsonArray parseUrlPair)
  img_src <- obj .:? "img_src" >>= \mb -> pure (mb >>= decodeJson)
  engine <- (obj .:? "engine") >>= \mb -> pure $ fromMaybe "unknown" (mb >>= decodeJson)
  
  pure
    { title: title
    , content: content
    , urls: urls
    , img_src: img_src
    , engine: engine
    }

parseUrlPair :: Json -> Either String { title :: String, url :: String }
parseUrlPair json = do
  obj <- decodeJson json
  title <- obj .: "title" >>= decodeJson
  url <- obj .: "url" >>= decodeJson
  pure { title, url }

-- Helper to decode JSON array
decodeJsonArray :: forall a. (Json -> Either String a) -> Json -> Either String (Array a)
decodeJsonArray decoder json = do
  arr <- decodeJson json
  traverse decoder arr

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
mkSearchProof :: SearXNGConfig -> SearchResult -> Effect NetworkAccess
mkSearchProof config result = do
  timestamp <- nowMillis
  let resultJson = encodeJson result
  let responseHash = hashString resultJson
  pure
    { url: config.baseUrl
    , responseHash: responseHash
    , timestamp: timestamp
    }


-- ============================================================================
-- HELPERS
-- ============================================================================

notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> Effect a
