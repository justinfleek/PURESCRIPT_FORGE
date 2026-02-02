{-|
Module      : Tool.Search
Description : Privacy-respecting web search via SearXNG
Copyright   : (c) Anomaly 2025
License     : AGPL-3.0

= SearXNG Metasearch Integration

This module provides web search capabilities through SearXNG, a free
privacy-respecting metasearch engine that aggregates results from
multiple sources without tracking.

== Module Structure

The Search module is split into sub-modules for maintainability:

* "Tool.Search.Types" - Type definitions (engines, categories, results)
* "Tool.Search.Query" - Query building and URL construction
* "Tool.Search.SearXNG" - HTTP client and SearXNG communication

== Privacy Guarantees

1. No user tracking or profiling
2. No search history storage
3. Proxy requests through SearXNG (user IP hidden from engines)
4. No JavaScript required for basic search
5. Instance can be self-hosted

== Coeffect Equation

@
  search : SearchParams -> Graded Network ToolResult

  -- Requires:
  -- 1. Network access to SearXNG instance
@

== Engines by Category

| Category  | Engines                                              |
|-----------|------------------------------------------------------|
| Web       | google, bing, duckduckgo, brave, qwant, startpage   |
| Images    | google images, bing images, flickr, unsplash        |
| Videos    | youtube, vimeo, dailymotion, peertube               |
| News      | google news, bing news, wikinews                    |
| Science   | arxiv, google scholar, semantic scholar, pubmed     |
| Code      | github, gitlab, codeberg, sourcegraph               |
| Files     | fdroid, apkmirror                                   |

-}
module Tool.Search
  ( -- * Tool Interface
    module Tool.Search.Types
  , module Tool.Search.Query
  , module Tool.Search.SearXNG
    -- * Execution
  , execute
  , searchTool
  ) where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Either (Either(..))
import Data.Argonaut (Json, class DecodeJson, encodeJson, decodeJson)
import Effect.Aff (Aff)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)

-- Re-exports
import Tool.Search.Types
import Tool.Search.Query
import Tool.Search.SearXNG

-- ============================================================================
-- TOOL INTERFACE
-- ============================================================================

-- | Execute search
execute :: SearchParams -> ToolContext -> Aff ToolResult
execute params _ctx = do
  -- 1. Validate parameters
  -- 2. Build SearXNG query URL
  -- 3. Make HTTP request to SearXNG instance
  -- 4. Parse JSON response
  -- 5. Format results
  pure
    { title: "Search: " <> params.query
    , metadata: encodeJson
        { query: params.query
        , categories: map show params.categories
        , limit: params.limit
        }
    , output: "TODO: Implement SearXNG search via HTTP FFI"
    , attachments: Nothing
    }

-- | Tool registration
searchTool :: ToolInfo
searchTool =
  { id: "search"
  , description: "Privacy-respecting web search via SearXNG metasearch"
  , parameters: encodeJson searchSchema
  , execute: \json ctx ->
      case decodeSearchParams json of
        Left err -> pure $ mkErrorResult (show err)
        Right params -> execute params ctx
  , formatValidationError: Just formatError
  }

-- ============================================================================
-- HELPERS
-- ============================================================================

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Search Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

formatError :: Json -> String
formatError _ = notImplemented "formatError"

searchSchema :: { type :: String }
searchSchema = notImplemented "searchSchema"

decodeSearchParams :: Json -> Either String SearchParams
decodeSearchParams _ = notImplemented "decodeSearchParams"

notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
