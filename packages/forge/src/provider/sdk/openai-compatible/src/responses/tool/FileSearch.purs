-- | File Search Tool
module Forge.Provider.SDK.OpenAICompatible.Responses.Tool.FileSearch where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)

-- | File search input
type FileSearchInput =
  { query :: String
  , vectorStoreIds :: Array String
  }

-- | File search result
type FileSearchResult =
  { fileId :: String
  , filename :: String
  , score :: Number
  , content :: String
  }

foreign import searchFFI :: String -> Array String -> Aff (Either String (Array FileSearchResult))

-- | Search files
search :: FileSearchInput -> Aff (Either String (Array FileSearchResult))
search input = searchFFI input.query input.vectorStoreIds
