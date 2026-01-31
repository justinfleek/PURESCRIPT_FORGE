-- | Web Search FFI Module
-- | Provides web search functionality via OpenCode SDK or external search API
module Bridge.FFI.Node.WebSearch where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either)
import Data.Maybe (Maybe)
import Bridge.FFI.Node.Handlers (WebSearchRequest, WebSearchResponse)

-- | Execute web search
-- | Uses OpenCode SDK web_search tool if available, otherwise falls back to external API
foreign import searchWeb :: WebSearchRequest -> Aff (Either String WebSearchResponse)
