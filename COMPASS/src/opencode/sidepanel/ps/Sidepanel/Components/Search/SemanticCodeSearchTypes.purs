{-|
Module      : Sidepanel.Components.Search.SemanticCodeSearchTypes
Description : Types for semantic code search
Types for semantic code search and pattern matching.
-}
module Sidepanel.Components.Search.SemanticCodeSearchTypes where

import Prelude

-- | Semantic search query
type SemanticSearchQuery =
  { text :: String  -- Search query
  , scope :: Maybe String  -- File or directory scope
  , language :: Maybe String  -- Language filter
  , resultType :: SearchResultType  -- Type of results to return
  , maxResults :: Int  -- Maximum number of results
  }

-- | Search result type
data SearchResultType
  = AllResults
  | FunctionsOnly
  | TypesOnly
  | ClassesOnly
  | ExamplesOnly

derive instance eqSearchResultType :: Eq SearchResultType

-- | Search result
type SearchResult =
  { file :: String
  , line :: Int
  , column :: Int
  , match :: String  -- Matched code snippet
  , context :: String  -- Surrounding context
  , relevance :: Number  -- Relevance score (0.0 to 1.0)
  , type_ :: SearchResultType
  }

-- | Pattern match
type PatternMatch =
  { file :: String
  , line :: Int
  , pattern :: String
  , match :: String
  , confidence :: Number
  }

-- | Code similarity
type CodeSimilarity =
  { file :: String
  , line :: Int
  , similarity :: Number  -- Similarity score (0.0 to 1.0)
  , code :: String
  }
