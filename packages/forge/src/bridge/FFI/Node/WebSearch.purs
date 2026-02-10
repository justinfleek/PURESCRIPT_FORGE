-- | Web Search FFI Module
-- | Provides web search functionality via OpenCode SDK or external search API
module Bridge.FFI.Node.WebSearch where

import Prelude
import Effect.Aff (Aff)
import Effect.Aff.Compat (EffectFnAff, fromEffectFnAff)
import Data.Either (Either)
import Bridge.FFI.Node.Handlers (WebSearchRequest, WebSearchResponse)

-- | FFI implementation
foreign import searchWebImpl :: WebSearchRequest -> EffectFnAff (Either String WebSearchResponse)

-- | Execute web search
-- | Uses OpenCode SDK web_search tool if available, otherwise falls back to external API
searchWeb :: WebSearchRequest -> Aff (Either String WebSearchResponse)
searchWeb req = fromEffectFnAff $ searchWebImpl req
