-- | File Search Tool
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/provider/sdk/openai-compatible/src/responses/tool/file-search.ts
module Opencode.Provider.SDK.OpenAICompatible.Responses.Tool.FileSearch where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Opencode.Util.NotImplemented (notImplemented)

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

-- | Search files
search :: FileSearchInput -> Aff (Either String (Array FileSearchResult))
search input = notImplemented "Tool.FileSearch.search"
