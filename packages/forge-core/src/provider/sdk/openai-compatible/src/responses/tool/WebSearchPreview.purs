-- | Web Search Preview Tool
-- | TODO: Implement based on _OTHER/forge-original/packages/forge/src/provider/sdk/openai-compatible/src/responses/tool/web-search-preview.ts
module Forge.Provider.SDK.OpenAICompatible.Responses.Tool.WebSearchPreview where

import Prelude
import Effect.Aff (Aff)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Forge.Util.NotImplemented (notImplemented)

-- | Web search preview input
type WebSearchPreviewInput =
  { url :: String
  }

-- | Web search preview output
type WebSearchPreviewOutput =
  { title :: Maybe String
  , description :: Maybe String
  , content :: String
  }

-- | Get preview of a URL
preview :: WebSearchPreviewInput -> Aff (Either String WebSearchPreviewOutput)
preview input = notImplemented "Tool.WebSearchPreview.preview"
