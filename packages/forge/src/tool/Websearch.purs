{-|
Module      : Forge.Tool.Websearch
Description : Web search via search API
= Web Search Tool

This module provides web search functionality for retrieving
information from the web.

== Coeffect Equation

@
  websearch : WebsearchParams -> Graded Network SearchResult

  -- Requires network access for search API
@

== Usage

@
  websearch { query: "purescript tutorial", limit: Just 10 }
@
-}
module Forge.Tool.Websearch
  ( -- * Tool Interface
    WebsearchParams(..)
  , SearchResult(..)
  , execute
  , websearchTool
  ) where

import Prelude

import Data.Maybe (Maybe(..), maybe)
import Data.Either (Either(..))
import Data.Array as Array
import Data.String as String
import Data.Argonaut (Json, encodeJson, decodeJson, (.:), (.:?), printJsonDecodeError)
import Effect.Aff (Aff)

-- ============================================================================
-- TYPES
-- ============================================================================

-- | Websearch tool parameters.
type WebsearchParams =
  { query :: String
  , limit :: Maybe Int
  }

-- | Single search result
type SearchResult =
  { title :: String
  , url :: String
  , snippet :: String
  }

-- | Search response
type SearchResponse =
  { results :: Array SearchResult
  , query :: String
  , totalResults :: Int
  }

-- | Tool result type
type ToolResult =
  { title :: String
  , output :: String
  , metadata :: Json
  , attachments :: Maybe (Array Json)
  }

-- | Tool context
type ToolContext = 
  { workspaceRoot :: String
  }

-- | Tool info
type ToolInfo =
  { id :: String
  , description :: String
  , parameters :: Json
  , execute :: Json -> ToolContext -> Aff ToolResult
  , formatValidationError :: Maybe (Json -> String)
  }

-- ============================================================================
-- EXECUTION
-- ============================================================================

execute :: WebsearchParams -> ToolContext -> Aff ToolResult
execute params ctx = do
  -- Validate query
  if String.null (String.trim params.query) then
    pure $ mkErrorResult "Query cannot be empty"
  else do
    let limit = maybe 10 identity params.limit
    
    -- Execute search via FFI
    result <- searchFFI params.query limit
    
    case result of
      Left err -> pure $ mkErrorResult err
      Right response -> do
        let numResults = Array.length response.results
        pure
          { title: "Search: " <> params.query
          , metadata: encodeJson
              { query: params.query
              , resultCount: numResults
              , limit
              }
          , output: formatResults response
          , attachments: Nothing
          }

-- | FFI for search execution
foreign import searchFFI :: String -> Int -> Aff (Either String SearchResponse)

-- ============================================================================
-- OUTPUT FORMATTING
-- ============================================================================

formatResults :: SearchResponse -> String
formatResults response =
  if Array.null response.results
  then "No results found for: " <> response.query
  else 
    let header = "Found " <> show (Array.length response.results) <> " results for: " <> response.query
        body = String.joinWith "\n\n" $ Array.mapWithIndex formatResult response.results
    in header <> "\n\n" <> body

formatResult :: Int -> SearchResult -> String
formatResult idx result =
  show (idx + 1) <> ". " <> result.title <> "\n" <>
  "   " <> result.url <> "\n" <>
  "   " <> result.snippet

-- ============================================================================
-- TOOL REGISTRATION
-- ============================================================================

websearchTool :: ToolInfo
websearchTool =
  { id: "websearch"
  , description: "Search the web for information"
  , parameters: websearchSchema
  , execute: \json ctx ->
      case decodeWebsearchParams json of
        Left err -> pure $ mkErrorResult err
        Right params -> execute params ctx
  , formatValidationError: Nothing
  }

websearchSchema :: Json
websearchSchema = encodeJson
  { "type": "object"
  , "properties":
      { "query":
          { "type": "string"
          , "description": "Search query text"
          }
      , "limit":
          { "type": "integer"
          , "description": "Maximum number of results (default: 10)"
          , "minimum": 1
          , "maximum": 100
          }
      }
  , "required": ["query"]
  }

decodeWebsearchParams :: Json -> Either String WebsearchParams
decodeWebsearchParams json =
  case decodeWebsearchParamsImpl json of
    Left err -> Left (printJsonDecodeError err)
    Right result -> Right result
  where
    decodeWebsearchParamsImpl j = do
      obj <- decodeJson j
      query <- obj .: "query"
      limit <- obj .:? "limit"
      pure { query, limit }

mkErrorResult :: String -> ToolResult
mkErrorResult err =
  { title: "Search Error"
  , metadata: encodeJson { error: err }
  , output: "Error: " <> err
  , attachments: Nothing
  }
