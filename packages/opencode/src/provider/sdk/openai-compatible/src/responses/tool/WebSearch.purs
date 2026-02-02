-- | Web Search Tool
-- | TODO: Implement based on _OTHER/opencode-original/packages/opencode/src/provider/sdk/openai-compatible/src/responses/tool/web-search.ts
module Opencode.Provider.SDK.OpenAICompatible.Responses.Tool.WebSearch where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Opencode.Util.NotImplemented (notImplemented)

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

-- | Search the web
search :: WebSearchInput -> Aff (Either String (Array WebSearchResult))
search input = notImplemented "Tool.WebSearch.search"
