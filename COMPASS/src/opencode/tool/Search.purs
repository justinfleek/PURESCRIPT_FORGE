{-|
Module      : Tool.Search
Description : Privacy-respecting web search via SearXNG
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

import Data.Maybe (Maybe(..), fromMaybe)
import Data.Either (Either(..))
import Data.Argonaut (Json, class DecodeJson, encodeJson, decodeJson, (.:), (.:?))
import Data.Array as Array
import Data.String as String
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Tool.Search.Types (Category(..), Engine(..), TimeRange(..), SafeSearchLevel(..))

import Opencode.Types.Tool (ToolContext, ToolResult, ToolInfo, ToolMetadata(..))

-- Re-exports
import Tool.Search.Types
import Tool.Search.Query (Query, buildUrl)
import Tool.Search.SearXNG (performSearch, defaultConfig, SearXNGConfig, SearchResult)

-- ============================================================================
-- TOOL INTERFACE
-- ============================================================================

-- | Execute search
execute :: SearchParams -> ToolContext -> Aff ToolResult
execute params _ctx = do
  -- 1. Build query from params
  let query = buildQuery params
  
  -- 2. Get SearXNG config (use default for now, could come from ctx)
  let config = defaultConfig
  
  -- 3. Perform search
  searchResult <- performSearch config query
  
  case searchResult of
    Left err -> pure $ mkErrorResult err
    Right result -> do
      -- 4. Format results
      let output = formatSearchResults result params
      pure
        { title: "Search: " <> params.query <> " (" <> show (Array.length result.results) <> " results)"
        , metadata: SearchMetadata
            { query: params.query
            , categories: map show params.categories
            , limit: params.limit
            , resultsCount: Array.length result.results
            , searchTimeMs: result.searchTimeMs
            }
        , output: output
        , attachments: Nothing
        }

-- | Build query from search params
buildQuery :: SearchParams -> Query
buildQuery params =
  { text: params.query
  , categories: params.categories
  , engines: params.engines
  , language: params.language
  , timeRange: params.timeRange
  , pageno: params.pageno
  }

-- | Format search results for output
formatSearchResults :: SearchResult -> SearchParams -> String
formatSearchResults result params =
  let header = "Search Results for: \"" <> params.query <> "\"\n" <>
               "Found " <> show (Array.length result.results) <> " results in " <>
               show result.searchTimeMs <> "ms\n\n"
      resultsText = if Array.null result.results
        then "No results found."
        else String.joinWith "\n\n" $ Array.mapWithIndex formatResultItem result.results
      infoboxesText = if Array.null result.infoboxes
        then ""
        else "\n\n--- Infoboxes ---\n" <>
             String.joinWith "\n\n" (Array.map formatInfobox result.infoboxes)
      suggestionsText = if Array.null result.suggestions
        then ""
        else "\n\n--- Suggestions ---\n" <>
             String.joinWith ", " result.suggestions
  in header <> resultsText <> infoboxesText <> suggestionsText

-- | Format a single result item
formatResultItem :: Int -> ResultItem -> String
formatResultItem idx item =
  show (idx + 1) <> ". " <> item.title <> "\n" <>
  "   URL: " <> item.url <> "\n" <>
  "   " <> item.content <> "\n" <>
  "   Engine: " <> item.engine <> " | Category: " <> show item.category <>
  (case item.publishedDate of
    Just date -> " | Published: " <> date
    Nothing -> "")

-- | Format an infobox
formatInfobox :: Infobox -> String
formatInfobox box =
  "**" <> box.title <> "**\n" <>
  box.content <>
  (if Array.null box.urls
    then ""
    else "\n\nRelated links:\n" <>
         String.joinWith "\n" (Array.map (\u -> "- [" <> u.title <> "](" <> u.url <> ")") box.urls))

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
  , metadata: ErrorMetadata { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }

formatError :: Json -> String
formatError json = case decodeJson json of
  Left err -> "Invalid search parameters: " <> err
  Right obj -> case obj .: "query" of
    Left _ -> "Missing required field: query"
    Right _ -> "Invalid search parameters"

searchSchema :: Json
searchSchema = encodeJson
  { type: "object"
  , properties:
      { query: { type: "string", description: "Search query text" }
      , categories: { type: "array", items: { type: "string" }, description: "Search categories (general, images, videos, etc.)" }
      , engines: { type: "array", items: { type: "string" }, description: "Specific search engines to use (optional)" }
      , language: { type: "string", description: "Language code (ISO 639-1)", default: "en" }
      , timeRange: { type: "string", enum: ["day", "week", "month", "year"], description: "Time range filter (optional)" }
      , safesearch: { type: "string", enum: ["off", "moderate", "strict"], description: "SafeSearch level", default: "moderate" }
      , pageno: { type: "integer", description: "Page number (1-indexed)", default: 1, minimum: 1 }
      , limit: { type: "integer", description: "Maximum number of results", default: 20, minimum: 1, maximum: 100 }
      }
  , required: ["query"]
  }

decodeSearchParams :: Json -> Either String SearchParams
decodeSearchParams json = do
  obj <- decodeJson json
  query <- obj .: "query" >>= decodeJson
  categories <- (obj .:? "categories" >>= \mb -> pure $ fromMaybe [] (mb >>= decodeJson)) # map (map parseCategory)
  engines <- (obj .:? "engines" >>= \mb -> pure (mb >>= decodeJson)) # map (map (map parseEngine))
  language <- (obj .:? "language" >>= \mb -> pure $ fromMaybe "en" (mb >>= decodeJson))
  timeRange <- (obj .:? "timeRange" >>= \mb -> pure (mb >>= decodeJson)) # map (map parseTimeRange)
  safesearch <- (obj .:? "safesearch" >>= \mb -> pure $ parseSafeSearch (fromMaybe "moderate" (mb >>= decodeJson)))
  pageno <- (obj .:? "pageno" >>= \mb -> pure $ fromMaybe 1 (mb >>= decodeJson))
  limit <- (obj .:? "limit" >>= \mb -> pure $ fromMaybe 20 (mb >>= decodeJson))
  pure { query, categories, engines, language, timeRange, safesearch, pageno, limit }
  where
    parseCategory :: String -> Category
    parseCategory "general" = General
    parseCategory "images" = Images
    parseCategory "videos" = Videos
    parseCategory "news" = News
    parseCategory "science" = Science
    parseCategory "it" = IT
    parseCategory "files" = Files
    parseCategory "socialmedia" = SocialMedia
    parseCategory _ = General
    
    parseEngine :: String -> Engine
    parseEngine s = case s of
      "google" -> Google
      "bing" -> Bing
      "duckduckgo" -> DuckDuckGo
      "brave" -> Brave
      "qwant" -> Qwant
      "startpage" -> StartPage
      "github" -> GitHub
      "gitlab" -> GitLab
      "stackoverflow" -> StackOverflow
      "sourcegraph" -> SourceGraph
      "hackernews" -> HackerNews
      "hackage" -> Hackage
      _ -> Google
    
    parseTimeRange :: String -> TimeRange
    parseTimeRange "day" = Day
    parseTimeRange "week" = Week
    parseTimeRange "month" = Month
    parseTimeRange "year" = Year
    parseTimeRange _ = Day
    
    parseSafeSearch :: String -> SafeSearchLevel
    parseSafeSearch "off" = SafeSearchOff
    parseSafeSearch "moderate" = SafeSearchModerate
    parseSafeSearch "strict" = SafeSearchStrict
    parseSafeSearch _ = SafeSearchModerate

notImplemented :: forall a. String -> a
notImplemented name = unsafeCrashWith ("Not implemented: " <> name)

foreign import unsafeCrashWith :: forall a. String -> a
