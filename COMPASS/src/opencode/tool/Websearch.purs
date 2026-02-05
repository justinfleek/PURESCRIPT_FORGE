{-|
Module      : Tool.Websearch
Description : Web search via SearXNG metasearch engine
= Web Search Tool

This module provides web search functionality through SearXNG,
delegating to the Tool.Search module for the actual implementation.

== System F-ω Encoding

Web search is a graded computation requiring network coeffects:

@
  -- Search indexed by backend
  websearch : ∀ (b :: SearchBackend).
    Query → Graded (Network ⊗ Search b) SearchResult

  -- Proof of search execution
  data SearchProof where
    MkSearchProof : NetworkAccess → QueryHash → SearchProof
@

== Privacy Model

SearXNG provides privacy-respecting search:

1. No user tracking
2. No search history
3. IP address hidden from search engines
4. Aggregated results from multiple sources
5. Self-hostable for complete control

== Usage

@
  import Tool.Websearch as Websearch

  result <- Websearch.execute
    { query: "system f omega type theory"
    , limit: Just 10
    }
@

-}
module Tool.Websearch
  ( -- * Tool Interface
    WebsearchParams(..)
    execute
  , websearchTool
    -- * Re-exports from Tool.Search
  , module ReExports
  ) where

import Prelude

import Data.Maybe (Maybe(..), maybe)
import Data.Either (Either(..))
import Data.Argonaut (Json, encodeJson, decodeJson, (.:), (.:?))
import Effect.Aff (Aff)

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo)
import Aleph.Coeffect (Resource(..), SearchBackend(..), network, searchRes, (⊗))

import Tool.Search 
  ( SearchParams
  , SearchResult
  , Category(..)
  , Engine(..)
  , Query
  , buildQuery
  , SearXNGConfig
  , defaultConfig
  ) as ReExports

import Tool.Search as Search

-- ════════════════════════════════════════════════════════════════════════════
-- TOOL INTERFACE
-- ════════════════════════════════════════════════════════════════════════════

{-| Websearch tool parameters.

Simplified interface for web search. For advanced usage, use Tool.Search directly.

@
  record WebsearchParams where
    query : String
    limit : Maybe Nat
@
-}
type WebsearchParams =
  { query :: String
  , limit :: Maybe Int
  }

-- | Execute web search
execute :: WebsearchParams -> Aff ToolResult
execute params = do
  let searchParams =
        { query: params.query
        , categories: [Search.General]
        , engines: Nothing
        , language: "en"
        , timeRange: Nothing
        , safesearch: Search.SafeSearchModerate
        , pageno: 1
        , limit: params.limit # maybe 10 identity
        }
  Search.execute searchParams defaultCtx
  where
    defaultCtx = 
      { sessionId: ""
      , permissions: []
      , config: {}
      }

-- | Tool registration
websearchTool :: ToolInfo
websearchTool =
  { id: "websearch"
  , description: "Privacy-respecting web search via SearXNG"
  , parameters: encodeJson websearchSchema
  , execute: \json ctx ->
      case decodeWebsearchParams json of
        Left err -> pure $ mkErrorResult err
        Right params -> executeWithContext params ctx
  , formatValidationError: Nothing
  }

-- | Execute with context
executeWithContext :: WebsearchParams -> ToolContext -> Aff ToolResult
executeWithContext params ctx = do
  let searchParams =
        { query: params.query
        , categories: [Search.General]
        , engines: Nothing
        , language: "en"
        , timeRange: Nothing
        , safesearch: Search.SafeSearchModerate
        , pageno: 1
        , limit: params.limit # maybe 10 identity
        }
  Search.execute searchParams ctx

-- ════════════════════════════════════════════════════════════════════════════
-- COEFFECTS
-- ════════════════════════════════════════════════════════════════════════════

{-| Coeffect for web search.

Web search requires network access and search backend:
@
  websearchCoeffect = Network ⊗ Search (SearXNG url)
@
-}
websearchCoeffect :: Resource
websearchCoeffect = network ⊗ searchRes (SearXNG Search.defaultConfig.baseUrl)

-- ════════════════════════════════════════════════════════════════════════════
-- HELPERS
-- ════════════════════════════════════════════════════════════════════════════

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Search Error"
  , metadata: ErrorMetadata { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

websearchSchema :: Json
websearchSchema = encodeJson
  { type: "object"
  , properties:
      { query: { type: "string", description: "Search query text" }
      , limit: { type: "integer", description: "Maximum number of results (default: 10)", minimum: 1, maximum: 100 }
      }
  , required: ["query"]
  }
