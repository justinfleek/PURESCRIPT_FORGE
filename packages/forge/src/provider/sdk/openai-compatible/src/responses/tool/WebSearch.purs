-- | Web Search Tool
module Forge.Provider.SDK.OpenAICompatible.Responses.Tool.WebSearch where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe(..))

-- | Web search input
type WebSearchInput =
  { query :: String
  , numResults :: Maybe Int
  }

-- | Web search result
type WebSearchResult =
  { title :: String
  , url :: String
  , snippet :: String
  }

foreign import searchFFI :: String -> Int -> Aff (Either String (Array WebSearchResult))

-- | Search the web
search :: WebSearchInput -> Aff (Either String (Array WebSearchResult))
search input = do
  let num = case input.numResults of
        Just n -> n
        Nothing -> 5
  searchFFI input.query num
